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
            let uu___132_64 = g1 in
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
                      (fun _0_28  -> FStar_Util.Inl _0_28) in
                  Some uu____76 in
                FStar_Syntax_Util.abs uu____67 f uu____69 in
              FStar_All.pipe_left
                (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                uu____66 in
            {
              FStar_TypeChecker_Env.guard_f = uu____65;
              FStar_TypeChecker_Env.deferred =
                (uu___132_64.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_64.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_64.FStar_TypeChecker_Env.implicits)
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
          let uu___133_104 = g in
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
              (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
              uu____106 in
          {
            FStar_TypeChecker_Env.guard_f = uu____105;
            FStar_TypeChecker_Env.deferred =
              (uu___133_104.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___133_104.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___133_104.FStar_TypeChecker_Env.implicits)
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
          let uu___134_145 = g in
          let uu____146 =
            let uu____147 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____147 in
          {
            FStar_TypeChecker_Env.guard_f = uu____146;
            FStar_TypeChecker_Env.deferred =
              (uu___134_145.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___134_145.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___134_145.FStar_TypeChecker_Env.implicits)
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
        let uu____201 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____201;
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
                       let uu____246 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____246
                       then f1
                       else FStar_Syntax_Util.mk_forall u (Prims.fst b) f1)
                us bs f in
            let uu___135_248 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___135_248.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_248.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_248.FStar_TypeChecker_Env.implicits)
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
               let uu____262 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____262
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
            let uu___136_275 = g in
            let uu____276 =
              let uu____277 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____277 in
            {
              FStar_TypeChecker_Env.guard_f = uu____276;
              FStar_TypeChecker_Env.deferred =
                (uu___136_275.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_275.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_275.FStar_TypeChecker_Env.implicits)
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
        | uu____322 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____337 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____337 in
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r in
            let uu____357 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app (uv1, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____357, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____390 = FStar_Syntax_Util.type_u () in
        match uu____390 with
        | (t_type,u) ->
            let uu____395 =
              let uu____398 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____398 t_type in
            (match uu____395 with
             | (tt,uu____400) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____421 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____447 -> false
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
    match projectee with | Success _0 -> true | uu____527 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____541 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____558 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____562 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____566 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___104_583  ->
    match uu___104_583 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____596 =
    let uu____597 = FStar_Syntax_Subst.compress t in
    uu____597.FStar_Syntax_Syntax.n in
  match uu____596 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____614 = FStar_Syntax_Print.uvar_to_string u in
      let uu____618 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____614 uu____618
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____621;
         FStar_Syntax_Syntax.pos = uu____622;
         FStar_Syntax_Syntax.vars = uu____623;_},args)
      ->
      let uu____651 = FStar_Syntax_Print.uvar_to_string u in
      let uu____655 = FStar_Syntax_Print.term_to_string ty in
      let uu____656 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____651 uu____655 uu____656
  | uu____657 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___105_663  ->
      match uu___105_663 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____667 =
            let uu____669 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____670 =
              let uu____672 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____673 =
                let uu____675 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____676 =
                  let uu____678 =
                    let uu____680 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____681 =
                      let uu____683 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____684 =
                        let uu____686 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____687 =
                          let uu____689 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____689] in
                        uu____686 :: uu____687 in
                      uu____683 :: uu____684 in
                    uu____680 :: uu____681 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____678 in
                uu____675 :: uu____676 in
              uu____672 :: uu____673 in
            uu____669 :: uu____670 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____667
      | FStar_TypeChecker_Common.CProb p ->
          let uu____694 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____695 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____694
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____695
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___106_701  ->
      match uu___106_701 with
      | UNIV (u,t) ->
          let x =
            let uu____705 = FStar_Options.hide_uvar_nums () in
            if uu____705
            then "?"
            else
              (let uu____707 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____707 FStar_Util.string_of_int) in
          let uu____709 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____709
      | TERM ((u,uu____711),t) ->
          let x =
            let uu____716 = FStar_Options.hide_uvar_nums () in
            if uu____716
            then "?"
            else
              (let uu____718 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____718 FStar_Util.string_of_int) in
          let uu____722 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____722
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____731 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____731 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____739 =
      let uu____741 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____741
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____739 (FStar_String.concat ", ")
let args_to_string args =
  let uu____759 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____767  ->
            match uu____767 with
            | (x,uu____771) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____759 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____776 =
      let uu____777 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____777 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____776;
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
        let uu___137_790 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___137_790.wl_deferred);
          ctr = (uu___137_790.ctr);
          defer_ok = (uu___137_790.defer_ok);
          smt_ok;
          tcenv = (uu___137_790.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___138_815 = empty_worklist env in
  let uu____816 = FStar_List.map Prims.snd g in
  {
    attempting = uu____816;
    wl_deferred = (uu___138_815.wl_deferred);
    ctr = (uu___138_815.ctr);
    defer_ok = false;
    smt_ok = (uu___138_815.smt_ok);
    tcenv = (uu___138_815.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___139_828 = wl in
        {
          attempting = (uu___139_828.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___139_828.ctr);
          defer_ok = (uu___139_828.defer_ok);
          smt_ok = (uu___139_828.smt_ok);
          tcenv = (uu___139_828.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___140_840 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___140_840.wl_deferred);
        ctr = (uu___140_840.ctr);
        defer_ok = (uu___140_840.defer_ok);
        smt_ok = (uu___140_840.smt_ok);
        tcenv = (uu___140_840.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____851 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____851
         then
           let uu____852 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____852
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___107_856  ->
    match uu___107_856 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___141_872 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___141_872.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___141_872.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___141_872.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___141_872.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___141_872.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___141_872.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___141_872.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___108_893  ->
    match uu___108_893 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_31  -> FStar_TypeChecker_Common.TProb _0_31)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.CProb _0_32)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___109_909  ->
      match uu___109_909 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___110_912  ->
    match uu___110_912 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___111_921  ->
    match uu___111_921 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___112_931  ->
    match uu___112_931 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___113_941  ->
    match uu___113_941 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___114_952  ->
    match uu___114_952 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___115_963  ->
    match uu___115_963 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___116_972  ->
    match uu___116_972 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_33  -> FStar_TypeChecker_Common.TProb _0_33) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.CProb _0_34) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____986 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____986 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____997  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1047 = next_pid () in
  let uu____1048 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1047;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1048;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1095 = next_pid () in
  let uu____1096 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1095;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1096;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1137 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1137;
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
        let uu____1189 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1189
        then
          let uu____1190 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1191 = prob_to_string env d in
          let uu____1192 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1190 uu____1191 uu____1192 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1197 -> failwith "impossible" in
           let uu____1198 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1206 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1207 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1206, uu____1207)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1211 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1212 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1211, uu____1212) in
           match uu____1198 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___117_1221  ->
            match uu___117_1221 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1228 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1231),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___118_1254  ->
           match uu___118_1254 with
           | UNIV uu____1256 -> None
           | TERM ((u,uu____1260),t) ->
               let uu____1264 = FStar_Unionfind.equivalent uv u in
               if uu____1264 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1283  ->
           match uu___119_1283 with
           | UNIV (u',t) ->
               let uu____1287 = FStar_Unionfind.equivalent u u' in
               if uu____1287 then Some t else None
           | uu____1291 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1298 =
        let uu____1299 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1299 in
      FStar_Syntax_Subst.compress uu____1298
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1306 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1306
let norm_arg env t =
  let uu____1325 = sn env (Prims.fst t) in (uu____1325, (Prims.snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1342  ->
              match uu____1342 with
              | (x,imp) ->
                  let uu____1349 =
                    let uu___142_1350 = x in
                    let uu____1351 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___142_1350.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___142_1350.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1351
                    } in
                  (uu____1349, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1366 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1366
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1369 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1369
        | uu____1371 -> u2 in
      let uu____1372 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1372
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1479 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1479 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1491;
               FStar_Syntax_Syntax.pos = uu____1492;
               FStar_Syntax_Syntax.vars = uu____1493;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1514 =
                 let uu____1515 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1516 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1515
                   uu____1516 in
               failwith uu____1514)
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1551 =
             let uu____1552 = FStar_Syntax_Subst.compress t1' in
             uu____1552.FStar_Syntax_Syntax.n in
           match uu____1551 with
           | FStar_Syntax_Syntax.Tm_refine uu____1564 -> aux true t1'
           | uu____1569 -> (t11, None))
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
        let uu____1604 =
          let uu____1605 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1606 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1605
            uu____1606 in
        failwith uu____1604 in
  let uu____1616 = whnf env t1 in aux false uu____1616
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1625 =
        let uu____1635 = empty_worklist env in
        base_and_refinement env uu____1635 t in
      FStar_All.pipe_right uu____1625 Prims.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1659 = FStar_Syntax_Syntax.null_bv t in
    (uu____1659, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1679 = base_and_refinement env wl t in
  match uu____1679 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____1738 =
  match uu____1738 with
  | (t_base,refopt) ->
      let uu____1752 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____1752 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___120_1776  ->
      match uu___120_1776 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1780 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1781 =
            let uu____1782 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____1782 in
          let uu____1783 =
            let uu____1784 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____1784 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1780 uu____1781
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1783
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1788 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1789 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____1790 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1788 uu____1789
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1790
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____1794 =
      let uu____1796 =
        let uu____1798 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1808  ->
                  match uu____1808 with | (uu____1812,uu____1813,x) -> x)) in
        FStar_List.append wl.attempting uu____1798 in
      FStar_List.map (wl_prob_to_string wl) uu____1796 in
    FStar_All.pipe_right uu____1794 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1831 =
          let uu____1841 =
            let uu____1842 = FStar_Syntax_Subst.compress k in
            uu____1842.FStar_Syntax_Syntax.n in
          match uu____1841 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____1883 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____1883)
              else
                (let uu____1897 = FStar_Syntax_Util.abs_formals t in
                 match uu____1897 with
                 | (ys',t1,uu____1918) ->
                     let uu____1931 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____1931))
          | uu____1952 ->
              let uu____1953 =
                let uu____1959 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____1959) in
              ((ys, t), uu____1953) in
        match uu____1831 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2014 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2014 c in
               let uu____2016 =
                 let uu____2023 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                 FStar_All.pipe_right uu____2023 (fun _0_36  -> Some _0_36) in
               FStar_Syntax_Util.abs ys1 t1 uu____2016)
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
            let uu____2074 = p_guard prob in
            match uu____2074 with
            | (uu____2077,uv) ->
                ((let uu____2080 =
                    let uu____2081 = FStar_Syntax_Subst.compress uv in
                    uu____2081.FStar_Syntax_Syntax.n in
                  match uu____2080 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2101 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2101
                        then
                          let uu____2102 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2103 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2104 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2102
                            uu____2103 uu____2104
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2108 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___143_2111 = wl in
                  {
                    attempting = (uu___143_2111.attempting);
                    wl_deferred = (uu___143_2111.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___143_2111.defer_ok);
                    smt_ok = (uu___143_2111.smt_ok);
                    tcenv = (uu___143_2111.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2124 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2124
         then
           let uu____2125 = FStar_Util.string_of_int pid in
           let uu____2126 =
             let uu____2127 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2127 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2125 uu____2126
         else ());
        commit sol;
        (let uu___144_2132 = wl in
         {
           attempting = (uu___144_2132.attempting);
           wl_deferred = (uu___144_2132.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___144_2132.defer_ok);
           smt_ok = (uu___144_2132.smt_ok);
           tcenv = (uu___144_2132.tcenv)
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
            | (uu____2161,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2169 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2169 in
          (let uu____2175 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2175
           then
             let uu____2176 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2177 =
               let uu____2178 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2178 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2176 uu____2177
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2203 =
    let uu____2207 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2207 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2203
    (FStar_Util.for_some
       (fun uu____2228  ->
          match uu____2228 with
          | (uv,uu____2236) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2280 = occurs wl uk t in Prims.op_Negation uu____2280 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2285 =
         let uu____2286 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk) in
         let uu____2290 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2286 uu____2290 in
       Some uu____2285) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2338 = occurs_check env wl uk t in
  match uu____2338 with
  | (occurs_ok,msg) ->
      let uu____2355 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2355, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set v1 in
  let uu____2419 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2443  ->
            fun uu____2444  ->
              match (uu____2443, uu____2444) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2487 =
                    let uu____2488 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2488 in
                  if uu____2487
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2502 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2502
                     then
                       let uu____2509 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2509)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2419 with | (isect,uu____2531) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2580  ->
          fun uu____2581  ->
            match (uu____2580, uu____2581) with
            | ((a,uu____2591),(b,uu____2593)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (Prims.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2637 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2643  ->
                match uu____2643 with
                | (b,uu____2647) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2637 then None else Some (a, (Prims.snd hd1))
  | uu____2656 -> None
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
            let uu____2699 = pat_var_opt env seen hd1 in
            (match uu____2699 with
             | None  ->
                 ((let uu____2707 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2707
                   then
                     let uu____2708 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (Prims.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2708
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2720 =
      let uu____2721 = FStar_Syntax_Subst.compress t in
      uu____2721.FStar_Syntax_Syntax.n in
    match uu____2720 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2737 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2799;
         FStar_Syntax_Syntax.pos = uu____2800;
         FStar_Syntax_Syntax.vars = uu____2801;_},args)
      -> (t, uv, k, args)
  | uu____2842 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____2896 = destruct_flex_t t in
  match uu____2896 with
  | (t1,uv,k,args) ->
      let uu____2964 = pat_vars env [] args in
      (match uu____2964 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3020 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option*
  FStar_Syntax_Syntax.delta_depth Prims.option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3068 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option*
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3091 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3095 -> false
let head_match: match_result -> match_result =
  fun uu___121_3098  ->
    match uu___121_3098 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3107 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3120 ->
          let uu____3121 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3121 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3131 -> fv.FStar_Syntax_Syntax.fv_delta)
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
          let uu____3199 = fv_delta_depth env fv in Some uu____3199
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
            let uu____3218 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3218
            then FullMatch
            else
              (let uu____3220 =
                 let uu____3225 =
                   let uu____3227 = fv_delta_depth env f in Some uu____3227 in
                 let uu____3228 =
                   let uu____3230 = fv_delta_depth env g in Some uu____3230 in
                 (uu____3225, uu____3228) in
               MisMatch uu____3220)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3234),FStar_Syntax_Syntax.Tm_uinst (g,uu____3236)) ->
            let uu____3245 = head_matches env f g in
            FStar_All.pipe_right uu____3245 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3252),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3254)) ->
            let uu____3279 = FStar_Unionfind.equivalent uv uv' in
            if uu____3279 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3287),FStar_Syntax_Syntax.Tm_refine (y,uu____3289)) ->
            let uu____3298 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3298 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3300),uu____3301) ->
            let uu____3306 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3306 head_match
        | (uu____3307,FStar_Syntax_Syntax.Tm_refine (x,uu____3309)) ->
            let uu____3314 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3314 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3320),FStar_Syntax_Syntax.Tm_app (head',uu____3322))
            ->
            let uu____3351 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3351 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3353),uu____3354) ->
            let uu____3369 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3369 head_match
        | (uu____3370,FStar_Syntax_Syntax.Tm_app (head1,uu____3372)) ->
            let uu____3387 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3387 head_match
        | uu____3388 ->
            let uu____3391 =
              let uu____3396 = delta_depth_of_term env t11 in
              let uu____3398 = delta_depth_of_term env t21 in
              (uu____3396, uu____3398) in
            MisMatch uu____3391
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3434 = FStar_Syntax_Util.head_and_args t in
    match uu____3434 with
    | (head1,uu____3446) ->
        let uu____3461 =
          let uu____3462 = FStar_Syntax_Util.un_uinst head1 in
          uu____3462.FStar_Syntax_Syntax.n in
        (match uu____3461 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3467 =
               let uu____3468 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3468 FStar_Option.isSome in
             if uu____3467
             then
               let uu____3482 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3482 (fun _0_37  -> Some _0_37)
             else None
         | uu____3485 -> None) in
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
          (let uu____3565 =
             let uu____3570 = maybe_inline t11 in
             let uu____3572 = maybe_inline t21 in (uu____3570, uu____3572) in
           match uu____3565 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3597 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____3597 with
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
        let uu____3612 =
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
             let uu____3620 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____3620)) in
        (match uu____3612 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3628 -> fail r
    | uu____3633 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3658 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3688 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3703 = FStar_Syntax_Util.type_u () in
      match uu____3703 with
      | (t,uu____3707) ->
          let uu____3708 = new_uvar r binders t in Prims.fst uu____3708
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3717 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____3717 Prims.fst
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
        let uu____3759 = head_matches env t1 t' in
        match uu____3759 with
        | MisMatch uu____3760 -> false
        | uu____3765 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3825,imp),T (t2,uu____3828)) -> (t2, imp)
                     | uu____3845 -> failwith "Bad reconstruction") args
                args' in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1)))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3889  ->
                    match uu____3889 with
                    | (t2,uu____3897) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3930 = failwith "Bad reconstruction" in
          let uu____3931 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3931 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3984))::tcs2) ->
                       aux
                         (((let uu___145_4006 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___145_4006.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___145_4006.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4016 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___122_4047 =
                 match uu___122_4047 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4110 = decompose1 [] bs1 in
               (rebuild, matches, uu____4110))
      | uu____4138 ->
          let rebuild uu___123_4143 =
            match uu___123_4143 with
            | [] -> t1
            | uu____4145 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___124_4164  ->
    match uu___124_4164 with
    | T (t,uu____4166) -> t
    | uu____4175 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___125_4178  ->
    match uu___125_4178 with
    | T (t,uu____4180) -> FStar_Syntax_Syntax.as_arg t
    | uu____4189 -> failwith "Impossible"
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
              | (uu____4258,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4277 = new_uvar r scope1 k in
                  (match uu____4277 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4289 ->
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_app (gi, args))) None
                               r in
                       let uu____4308 =
                         let uu____4309 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_38  ->
                              FStar_TypeChecker_Common.TProb _0_38)
                           uu____4309 in
                       ((T (gi_xs, mk_kind)), uu____4308))
              | (uu____4318,uu____4319,C uu____4320) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4407 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4418;
                         FStar_Syntax_Syntax.pos = uu____4419;
                         FStar_Syntax_Syntax.vars = uu____4420;_})
                        ->
                        let uu____4435 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4435 with
                         | (T (gi_xs,uu____4451),prob) ->
                             let uu____4461 =
                               let uu____4462 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_39  -> C _0_39)
                                 uu____4462 in
                             (uu____4461, [prob])
                         | uu____4464 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4474;
                         FStar_Syntax_Syntax.pos = uu____4475;
                         FStar_Syntax_Syntax.vars = uu____4476;_})
                        ->
                        let uu____4491 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4491 with
                         | (T (gi_xs,uu____4507),prob) ->
                             let uu____4517 =
                               let uu____4518 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4518 in
                             (uu____4517, [prob])
                         | uu____4520 -> failwith "impossible")
                    | (uu____4526,uu____4527,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4529;
                         FStar_Syntax_Syntax.pos = uu____4530;
                         FStar_Syntax_Syntax.vars = uu____4531;_})
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
                        let uu____4605 =
                          let uu____4610 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____4610 FStar_List.unzip in
                        (match uu____4605 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____4639 =
                                 let uu____4640 =
                                   let uu____4643 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____4643 un_T in
                                 let uu____4644 =
                                   let uu____4650 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____4650
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____4640;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____4644;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____4639 in
                             ((C gi_xs), sub_probs))
                    | uu____4655 ->
                        let uu____4662 = sub_prob scope1 args q in
                        (match uu____4662 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4407 with
                   | (tc,probs) ->
                       let uu____4680 =
                         match q with
                         | (Some b,uu____4706,uu____4707) ->
                             let uu____4715 =
                               let uu____4719 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____4719 :: args in
                             ((Some b), (b :: scope1), uu____4715)
                         | uu____4737 -> (None, scope1, args) in
                       (match uu____4680 with
                        | (bopt,scope2,args1) ->
                            let uu____4780 = aux scope2 args1 qs2 in
                            (match uu____4780 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____4801 =
                                         let uu____4803 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst)) in
                                         f :: uu____4803 in
                                       FStar_Syntax_Util.mk_conj_l uu____4801
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (Prims.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____4816 =
                                         let uu____4818 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (Prims.fst b) f in
                                         let uu____4819 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst)) in
                                         uu____4818 :: uu____4819 in
                                       FStar_Syntax_Util.mk_conj_l uu____4816 in
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
  let uu___146_4872 = p in
  let uu____4875 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____4876 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___146_4872.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4875;
    FStar_TypeChecker_Common.relation =
      (uu___146_4872.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4876;
    FStar_TypeChecker_Common.element =
      (uu___146_4872.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___146_4872.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___146_4872.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___146_4872.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___146_4872.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___146_4872.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____4886 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____4886
            (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
      | FStar_TypeChecker_Common.CProb uu____4891 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____4905 = compress_prob wl pr in
        FStar_All.pipe_right uu____4905 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4911 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____4911 with
           | (lh,uu____4924) ->
               let uu____4939 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____4939 with
                | (rh,uu____4952) ->
                    let uu____4967 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4976,FStar_Syntax_Syntax.Tm_uvar uu____4977)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5002,uu____5003)
                          ->
                          let uu____5012 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5012 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5052 ->
                                    let rank =
                                      let uu____5059 = is_top_level_prob prob in
                                      if uu____5059
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5061 =
                                      let uu___147_5064 = tp in
                                      let uu____5067 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___147_5064.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___147_5064.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___147_5064.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5067;
                                        FStar_TypeChecker_Common.element =
                                          (uu___147_5064.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___147_5064.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___147_5064.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___147_5064.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___147_5064.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___147_5064.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5061)))
                      | (uu____5077,FStar_Syntax_Syntax.Tm_uvar uu____5078)
                          ->
                          let uu____5087 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5087 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5127 ->
                                    let uu____5133 =
                                      let uu___148_5138 = tp in
                                      let uu____5141 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5138.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5141;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5138.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___148_5138.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5138.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5138.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5138.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5138.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5138.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5138.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5133)))
                      | (uu____5157,uu____5158) -> (rigid_rigid, tp) in
                    (match uu____4967 with
                     | (rank,tp1) ->
                         let uu____5169 =
                           FStar_All.pipe_right
                             (let uu___149_5172 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___149_5172.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___149_5172.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___149_5172.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___149_5172.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___149_5172.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___149_5172.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___149_5172.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___149_5172.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___149_5172.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.TProb _0_42) in
                         (rank, uu____5169))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5178 =
            FStar_All.pipe_right
              (let uu___150_5181 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___150_5181.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___150_5181.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___150_5181.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___150_5181.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___150_5181.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___150_5181.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___150_5181.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___150_5181.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___150_5181.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43) in
          (rigid_rigid, uu____5178)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option*
      FStar_TypeChecker_Common.prob Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5213 probs =
      match uu____5213 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5243 = rank wl hd1 in
               (match uu____5243 with
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
    match projectee with | UDeferred _0 -> true | uu____5308 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5320 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5332 -> false
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
                        let uu____5369 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5369 with
                        | (k,uu____5373) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5378 -> false)))
            | uu____5379 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5422 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5422 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5425 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5431 =
                     let uu____5432 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5433 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5432
                       uu____5433 in
                   UFailed uu____5431)
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5450 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5450 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5453 ->
                let uu____5456 =
                  let uu____5457 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5458 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5457
                    uu____5458 msg in
                UFailed uu____5456 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5465 =
                let uu____5466 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5467 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5466 uu____5467 in
              failwith uu____5465
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5479 = FStar_Unionfind.equivalent v1 v2 in
              if uu____5479
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5492 = occurs_univ v1 u3 in
              if uu____5492
              then
                let uu____5493 =
                  let uu____5494 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5495 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5494 uu____5495 in
                try_umax_components u11 u21 uu____5493
              else
                (let uu____5497 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5497)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5507 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5507
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
  let uu____5578 = bc1 in
  match uu____5578 with
  | (bs1,mk_cod1) ->
      let uu____5603 = bc2 in
      (match uu____5603 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____5650 = FStar_Util.first_N n1 bs in
             match uu____5650 with
             | (bs3,rest) ->
                 let uu____5664 = mk_cod rest in (bs3, uu____5664) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____5682 =
               let uu____5686 = mk_cod1 [] in (bs1, uu____5686) in
             let uu____5688 =
               let uu____5692 = mk_cod2 [] in (bs2, uu____5692) in
             (uu____5682, uu____5688)
           else
             if l1 > l2
             then
               (let uu____5714 = curry l2 bs1 mk_cod1 in
                let uu____5721 =
                  let uu____5725 = mk_cod2 [] in (bs2, uu____5725) in
                (uu____5714, uu____5721))
             else
               (let uu____5734 =
                  let uu____5738 = mk_cod1 [] in (bs1, uu____5738) in
                let uu____5740 = curry l1 bs2 mk_cod2 in
                (uu____5734, uu____5740)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5844 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____5844
       then
         let uu____5845 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____5845
       else ());
      (let uu____5847 = next_prob probs in
       match uu____5847 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___151_5860 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___151_5860.wl_deferred);
               ctr = (uu___151_5860.ctr);
               defer_ok = (uu___151_5860.defer_ok);
               smt_ok = (uu___151_5860.smt_ok);
               tcenv = (uu___151_5860.tcenv)
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
                  let uu____5867 = solve_flex_rigid_join env tp probs1 in
                  (match uu____5867 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____5871 = solve_rigid_flex_meet env tp probs1 in
                     match uu____5871 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____5875,uu____5876) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5885 ->
                let uu____5890 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5918  ->
                          match uu____5918 with
                          | (c,uu____5923,uu____5924) -> c < probs.ctr)) in
                (match uu____5890 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____5946 =
                            FStar_List.map
                              (fun uu____5952  ->
                                 match uu____5952 with
                                 | (uu____5958,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____5946
                      | uu____5961 ->
                          let uu____5966 =
                            let uu___152_5967 = probs in
                            let uu____5968 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____5977  ->
                                      match uu____5977 with
                                      | (uu____5981,uu____5982,y) -> y)) in
                            {
                              attempting = uu____5968;
                              wl_deferred = rest;
                              ctr = (uu___152_5967.ctr);
                              defer_ok = (uu___152_5967.defer_ok);
                              smt_ok = (uu___152_5967.smt_ok);
                              tcenv = (uu___152_5967.tcenv)
                            } in
                          solve env uu____5966))))
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
            let uu____5989 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____5989 with
            | USolved wl1 ->
                let uu____5991 = solve_prob orig None [] wl1 in
                solve env uu____5991
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
                  let uu____6025 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6025 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6028 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6036;
                  FStar_Syntax_Syntax.pos = uu____6037;
                  FStar_Syntax_Syntax.vars = uu____6038;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6041;
                  FStar_Syntax_Syntax.pos = uu____6042;
                  FStar_Syntax_Syntax.vars = uu____6043;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6059 -> USolved wl
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
            ((let uu____6067 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6067
              then
                let uu____6068 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6068 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6076 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6076
         then
           let uu____6077 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6077
         else ());
        (let uu____6079 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6079 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6121 = head_matches_delta env () t1 t2 in
               match uu____6121 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6143 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6169 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6178 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6179 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6178, uu____6179)
                          | None  ->
                              let uu____6182 = FStar_Syntax_Subst.compress t1 in
                              let uu____6183 = FStar_Syntax_Subst.compress t2 in
                              (uu____6182, uu____6183) in
                        (match uu____6169 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6205 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_44  ->
                                    FStar_TypeChecker_Common.TProb _0_44)
                                 uu____6205 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6228 =
                                    let uu____6234 =
                                      let uu____6237 =
                                        let uu____6240 =
                                          let uu____6241 =
                                            let uu____6246 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6246) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6241 in
                                        FStar_Syntax_Syntax.mk uu____6240 in
                                      uu____6237 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6259 =
                                      let uu____6261 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6261] in
                                    (uu____6234, uu____6259) in
                                  Some uu____6228
                              | (uu____6270,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6272)) ->
                                  let uu____6277 =
                                    let uu____6281 =
                                      let uu____6283 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6283] in
                                    (t11, uu____6281) in
                                  Some uu____6277
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6289),uu____6290) ->
                                  let uu____6295 =
                                    let uu____6299 =
                                      let uu____6301 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6301] in
                                    (t21, uu____6299) in
                                  Some uu____6295
                              | uu____6306 ->
                                  let uu____6309 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6309 with
                                   | (head1,uu____6324) ->
                                       let uu____6339 =
                                         let uu____6340 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6340.FStar_Syntax_Syntax.n in
                                       (match uu____6339 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6347;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6349;_}
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
                                        | uu____6358 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6367) ->
                  let uu____6380 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___126_6389  ->
                            match uu___126_6389 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6394 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6394 with
                                      | (u',uu____6405) ->
                                          let uu____6420 =
                                            let uu____6421 = whnf env u' in
                                            uu____6421.FStar_Syntax_Syntax.n in
                                          (match uu____6420 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6425) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____6441 -> false))
                                 | uu____6442 -> false)
                            | uu____6444 -> false)) in
                  (match uu____6380 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6465 tps =
                         match uu____6465 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6492 =
                                    let uu____6497 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____6497 in
                                  (match uu____6492 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6516 -> None) in
                       let uu____6521 =
                         let uu____6526 =
                           let uu____6530 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____6530, []) in
                         make_lower_bound uu____6526 lower_bounds in
                       (match uu____6521 with
                        | None  ->
                            ((let uu____6537 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6537
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
                            ((let uu____6550 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6550
                              then
                                let wl' =
                                  let uu___153_6552 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___153_6552.wl_deferred);
                                    ctr = (uu___153_6552.ctr);
                                    defer_ok = (uu___153_6552.defer_ok);
                                    smt_ok = (uu___153_6552.smt_ok);
                                    tcenv = (uu___153_6552.tcenv)
                                  } in
                                let uu____6553 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6553
                              else ());
                             (let uu____6555 =
                                solve_t env eq_prob
                                  (let uu___154_6556 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___154_6556.wl_deferred);
                                     ctr = (uu___154_6556.ctr);
                                     defer_ok = (uu___154_6556.defer_ok);
                                     smt_ok = (uu___154_6556.smt_ok);
                                     tcenv = (uu___154_6556.tcenv)
                                   }) in
                              match uu____6555 with
                              | Success uu____6558 ->
                                  let wl1 =
                                    let uu___155_6560 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___155_6560.wl_deferred);
                                      ctr = (uu___155_6560.ctr);
                                      defer_ok = (uu___155_6560.defer_ok);
                                      smt_ok = (uu___155_6560.smt_ok);
                                      tcenv = (uu___155_6560.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____6562 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____6565 -> None))))
              | uu____6566 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6573 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6573
         then
           let uu____6574 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6574
         else ());
        (let uu____6576 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____6576 with
         | (u,args) ->
             let uu____6603 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____6603 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____6634 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____6634 with
                    | (h1,args1) ->
                        let uu____6662 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____6662 with
                         | (h2,uu____6675) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____6694 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____6694
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6707 =
                                          let uu____6709 =
                                            let uu____6710 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_45  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_45) uu____6710 in
                                          [uu____6709] in
                                        Some uu____6707))
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
                                       (let uu____6732 =
                                          let uu____6734 =
                                            let uu____6735 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____6735 in
                                          [uu____6734] in
                                        Some uu____6732))
                                  else None
                              | uu____6743 -> None)) in
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
                             let uu____6809 =
                               let uu____6815 =
                                 let uu____6818 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____6818 in
                               (uu____6815, m1) in
                             Some uu____6809)
                    | (uu____6827,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6829)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6861),uu____6862) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____6893 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6927) ->
                       let uu____6940 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___127_6949  ->
                                 match uu___127_6949 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6954 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____6954 with
                                           | (u',uu____6965) ->
                                               let uu____6980 =
                                                 let uu____6981 = whnf env u' in
                                                 uu____6981.FStar_Syntax_Syntax.n in
                                               (match uu____6980 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6985) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7001 -> false))
                                      | uu____7002 -> false)
                                 | uu____7004 -> false)) in
                       (match uu____6940 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7029 tps =
                              match uu____7029 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7070 =
                                         let uu____7077 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7077 in
                                       (match uu____7070 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7112 -> None) in
                            let uu____7119 =
                              let uu____7126 =
                                let uu____7132 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7132, []) in
                              make_upper_bound uu____7126 upper_bounds in
                            (match uu____7119 with
                             | None  ->
                                 ((let uu____7141 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7141
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
                                 ((let uu____7160 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7160
                                   then
                                     let wl' =
                                       let uu___156_7162 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___156_7162.wl_deferred);
                                         ctr = (uu___156_7162.ctr);
                                         defer_ok = (uu___156_7162.defer_ok);
                                         smt_ok = (uu___156_7162.smt_ok);
                                         tcenv = (uu___156_7162.tcenv)
                                       } in
                                     let uu____7163 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7163
                                   else ());
                                  (let uu____7165 =
                                     solve_t env eq_prob
                                       (let uu___157_7166 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___157_7166.wl_deferred);
                                          ctr = (uu___157_7166.ctr);
                                          defer_ok = (uu___157_7166.defer_ok);
                                          smt_ok = (uu___157_7166.smt_ok);
                                          tcenv = (uu___157_7166.tcenv)
                                        }) in
                                   match uu____7165 with
                                   | Success uu____7168 ->
                                       let wl1 =
                                         let uu___158_7170 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___158_7170.wl_deferred);
                                           ctr = (uu___158_7170.ctr);
                                           defer_ok =
                                             (uu___158_7170.defer_ok);
                                           smt_ok = (uu___158_7170.smt_ok);
                                           tcenv = (uu___158_7170.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7172 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7175 -> None))))
                   | uu____7176 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7241 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7241
                      then
                        let uu____7242 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7242
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___159_7274 = hd1 in
                      let uu____7275 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___159_7274.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___159_7274.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7275
                      } in
                    let hd21 =
                      let uu___160_7279 = hd2 in
                      let uu____7280 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7279.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7279.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7280
                      } in
                    let prob =
                      let uu____7284 =
                        let uu____7287 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7287 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_47  -> FStar_TypeChecker_Common.TProb _0_47)
                        uu____7284 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7295 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7295 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7298 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7298 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7316 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst in
                           let uu____7319 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7316 uu____7319 in
                         ((let uu____7325 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7325
                           then
                             let uu____7326 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7327 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7326 uu____7327
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7342 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7348 = aux scope env [] bs1 bs2 in
              match uu____7348 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7364 = compress_tprob wl problem in
        solve_t' env uu____7364 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7397 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7397 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7414,uu____7415) ->
                   let may_relate head3 =
                     let uu____7430 =
                       let uu____7431 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7431.FStar_Syntax_Syntax.n in
                     match uu____7430 with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7437 -> false in
                   let uu____7438 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7438
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
                                let uu____7455 =
                                  let uu____7456 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7456 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7455 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7458 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____7458
                   else giveup env1 "head mismatch" orig
               | (uu____7460,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___161_7468 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___161_7468.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___161_7468.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___161_7468.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___161_7468.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___161_7468.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___161_7468.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___161_7468.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___161_7468.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7469,None ) ->
                   ((let uu____7476 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7476
                     then
                       let uu____7477 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____7478 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____7479 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____7480 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7477
                         uu____7478 uu____7479 uu____7480
                     else ());
                    (let uu____7482 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____7482 with
                     | (head11,args1) ->
                         let uu____7508 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____7508 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7548 =
                                  let uu____7549 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____7550 = args_to_string args1 in
                                  let uu____7551 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____7552 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7549 uu____7550 uu____7551
                                    uu____7552 in
                                giveup env1 uu____7548 orig
                              else
                                (let uu____7554 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7557 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____7557 = FStar_Syntax_Util.Equal) in
                                 if uu____7554
                                 then
                                   let uu____7558 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____7558 with
                                   | USolved wl2 ->
                                       let uu____7560 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____7560
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7564 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____7564 with
                                    | (base1,refinement1) ->
                                        let uu____7590 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____7590 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____7644 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____7644 with
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
                                                           (fun uu____7654 
                                                              ->
                                                              fun uu____7655 
                                                                ->
                                                                match 
                                                                  (uu____7654,
                                                                    uu____7655)
                                                                with
                                                                | ((a,uu____7665),
                                                                   (a',uu____7667))
                                                                    ->
                                                                    let uu____7672
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
                                                                    _0_48  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_48)
                                                                    uu____7672)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____7678 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                Prims.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____7678 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____7682 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___162_7715 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___162_7715.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____7735 = p in
          match uu____7735 with
          | (((u,k),xs,c),ps,(h,uu____7746,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7795 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____7795 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____7809 = h gs_xs in
                     let uu____7810 =
                       let uu____7817 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_49  -> FStar_Util.Inl _0_49) in
                       FStar_All.pipe_right uu____7817
                         (fun _0_50  -> Some _0_50) in
                     FStar_Syntax_Util.abs xs1 uu____7809 uu____7810 in
                   ((let uu____7848 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7848
                     then
                       let uu____7849 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____7850 = FStar_Syntax_Print.comp_to_string c in
                       let uu____7851 = FStar_Syntax_Print.term_to_string im in
                       let uu____7852 = FStar_Syntax_Print.tag_of_term im in
                       let uu____7853 =
                         let uu____7854 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____7854
                           (FStar_String.concat ", ") in
                       let uu____7857 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____7849 uu____7850 uu____7851 uu____7852
                         uu____7853 uu____7857
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___128_7875 =
          match uu___128_7875 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____7904 = p in
          match uu____7904 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7962 = FStar_List.nth ps i in
              (match uu____7962 with
               | (pi,uu____7965) ->
                   let uu____7970 = FStar_List.nth xs i in
                   (match uu____7970 with
                    | (xi,uu____7977) ->
                        let rec gs k =
                          let uu____7986 = FStar_Syntax_Util.arrow_formals k in
                          match uu____7986 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8038)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8046 = new_uvar r xs k_a in
                                    (match uu____8046 with
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
                                         let uu____8065 = aux subst2 tl1 in
                                         (match uu____8065 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8080 =
                                                let uu____8082 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8082 :: gi_xs' in
                                              let uu____8083 =
                                                let uu____8085 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8085 :: gi_ps' in
                                              (uu____8080, uu____8083))) in
                              aux [] bs in
                        let uu____8088 =
                          let uu____8089 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8089 in
                        if uu____8088
                        then None
                        else
                          (let uu____8092 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8092 with
                           | (g_xs,uu____8099) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8106 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8111 =
                                   let uu____8118 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_51  -> FStar_Util.Inl _0_51) in
                                   FStar_All.pipe_right uu____8118
                                     (fun _0_52  -> Some _0_52) in
                                 FStar_Syntax_Util.abs xs uu____8106
                                   uu____8111 in
                               let sub1 =
                                 let uu____8149 =
                                   let uu____8152 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8159 =
                                     let uu____8162 =
                                       FStar_List.map
                                         (fun uu____8168  ->
                                            match uu____8168 with
                                            | (uu____8173,uu____8174,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8162 in
                                   mk_problem (p_scope orig) orig uu____8152
                                     (p_rel orig) uu____8159 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_53  ->
                                      FStar_TypeChecker_Common.TProb _0_53)
                                   uu____8149 in
                               ((let uu____8184 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8184
                                 then
                                   let uu____8185 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8186 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8185 uu____8186
                                 else ());
                                (let wl2 =
                                   let uu____8189 =
                                     let uu____8191 =
                                       FStar_All.pipe_left Prims.fst
                                         (p_guard sub1) in
                                     Some uu____8191 in
                                   solve_prob orig uu____8189
                                     [TERM (u, proj)] wl1 in
                                 let uu____8196 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_54  -> Some _0_54) uu____8196))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8220 = lhs in
          match uu____8220 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8243 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8243 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8265 =
                        let uu____8291 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8291) in
                      Some uu____8265
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8374 =
                           let uu____8378 =
                             let uu____8379 = FStar_Syntax_Subst.compress k in
                             uu____8379.FStar_Syntax_Syntax.n in
                           (uu____8378, args) in
                         match uu____8374 with
                         | (uu____8386,[]) ->
                             let uu____8388 =
                               let uu____8394 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8394) in
                             Some uu____8388
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____8411 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8411 with
                              | (uv1,uv_args) ->
                                  let uu____8440 =
                                    let uu____8441 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8441.FStar_Syntax_Syntax.n in
                                  (match uu____8440 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8448) ->
                                       let uu____8461 =
                                         pat_vars env [] uv_args in
                                       (match uu____8461 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8475  ->
                                                      let uu____8476 =
                                                        let uu____8477 =
                                                          let uu____8478 =
                                                            let uu____8481 =
                                                              let uu____8482
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____8482
                                                                Prims.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8481 in
                                                          Prims.fst
                                                            uu____8478 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8477 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8476)) in
                                            let c1 =
                                              let uu____8488 =
                                                let uu____8489 =
                                                  let uu____8492 =
                                                    let uu____8493 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8493 Prims.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8492 in
                                                Prims.fst uu____8489 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8488 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____8502 =
                                                let uu____8509 =
                                                  let uu____8515 =
                                                    let uu____8516 =
                                                      let uu____8519 =
                                                        let uu____8520 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____8520
                                                          Prims.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____8519 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____8516 in
                                                  FStar_Util.Inl uu____8515 in
                                                Some uu____8509 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8502 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____8543 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8548)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____8574 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____8574
                                 (fun _0_55  -> Some _0_55)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8593 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____8593 with
                                  | (args1,rest) ->
                                      let uu____8609 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____8609 with
                                       | (xs2,c2) ->
                                           let uu____8617 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____8617
                                             (fun uu____8628  ->
                                                match uu____8628 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____8650 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____8650 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____8696 =
                                        let uu____8699 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____8699 in
                                      FStar_All.pipe_right uu____8696
                                        (fun _0_56  -> Some _0_56))
                         | uu____8707 ->
                             let uu____8711 =
                               let uu____8712 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____8716 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____8717 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____8712 uu____8716 uu____8717 in
                             failwith uu____8711 in
                       let uu____8721 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____8721
                         (fun uu____8749  ->
                            match uu____8749 with
                            | (xs1,c1) ->
                                let uu____8777 =
                                  let uu____8800 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____8800) in
                                Some uu____8777)) in
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
                     let uu____8872 = imitate orig env wl1 st in
                     match uu____8872 with
                     | Failed uu____8877 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____8883 = project orig env wl1 i st in
                      match uu____8883 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____8901 = FStar_Syntax_Util.head_and_args t21 in
                match uu____8901 with
                | (hd1,uu____8912) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____8930 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____8933 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____8933
                         then true
                         else
                           ((let uu____8936 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____8936
                             then
                               let uu____8937 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____8937
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____8945 =
                    let uu____8948 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____8948 Prims.fst in
                  FStar_All.pipe_right uu____8945 FStar_Syntax_Free.names in
                let uu____8979 = FStar_Util.set_is_empty fvs_hd in
                if uu____8979
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____8988 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____8988 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____8996 =
                            let uu____8997 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____8997 in
                          giveup_or_defer1 orig uu____8996
                        else
                          (let uu____8999 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____8999
                           then
                             let uu____9000 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9000
                              then
                                let uu____9001 = subterms args_lhs in
                                imitate' orig env wl1 uu____9001
                              else
                                ((let uu____9005 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9005
                                  then
                                    let uu____9006 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9007 = names_to_string fvs1 in
                                    let uu____9008 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9006 uu____9007 uu____9008
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9013 ->
                                        let uu____9014 = sn_binders env vars in
                                        u_abs k_uv uu____9014 t21 in
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
                               (let uu____9023 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9023
                                then
                                  ((let uu____9025 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9025
                                    then
                                      let uu____9026 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9027 = names_to_string fvs1 in
                                      let uu____9028 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9026 uu____9027 uu____9028
                                    else ());
                                   (let uu____9030 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9030
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
                     (let uu____9041 =
                        let uu____9042 = FStar_Syntax_Free.names t1 in
                        check_head uu____9042 t2 in
                      if uu____9041
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9046 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9046
                          then
                            let uu____9047 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9047
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9050 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9050 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9092 =
               match uu____9092 with
               | (t,u,k,args) ->
                   let uu____9122 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9122 with
                    | (all_formals,uu____9133) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9225  ->
                                        match uu____9225 with
                                        | (x,imp) ->
                                            let uu____9232 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9232, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9240 = FStar_Syntax_Util.type_u () in
                                match uu____9240 with
                                | (t1,uu____9244) ->
                                    let uu____9245 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    Prims.fst uu____9245 in
                              let uu____9248 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9248 with
                               | (t',tm_u1) ->
                                   let uu____9255 = destruct_flex_t t' in
                                   (match uu____9255 with
                                    | (uu____9275,u1,k1,uu____9278) ->
                                        let sol =
                                          let uu____9306 =
                                            let uu____9311 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____9311) in
                                          TERM uu____9306 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9371 = pat_var_opt env pat_args hd1 in
                              (match uu____9371 with
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
                                              (fun uu____9400  ->
                                                 match uu____9400 with
                                                 | (x,uu____9404) ->
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
                                      let uu____9410 =
                                        let uu____9411 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____9411 in
                                      if uu____9410
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9415 =
                                           FStar_Util.set_add
                                             (Prims.fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9415 formals1
                                           tl1)))
                          | uu____9421 -> failwith "Impossible" in
                        let uu____9432 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____9432 all_formals args) in
             let solve_both_pats wl1 uu____9480 uu____9481 r =
               match (uu____9480, uu____9481) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9635 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____9635
                   then
                     let uu____9639 = solve_prob orig None [] wl1 in
                     solve env uu____9639
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____9654 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____9654
                       then
                         let uu____9655 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____9656 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____9657 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____9658 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____9659 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9655 uu____9656 uu____9657 uu____9658
                           uu____9659
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____9701 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____9701 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____9709 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____9709 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____9739 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____9739 in
                                  let uu____9742 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____9742 k3)
                           else
                             (let uu____9745 =
                                let uu____9746 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____9747 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____9748 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____9746 uu____9747 uu____9748 in
                              failwith uu____9745) in
                       let uu____9749 =
                         let uu____9755 =
                           let uu____9763 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____9763 in
                         match uu____9755 with
                         | (bs,k1') ->
                             let uu____9781 =
                               let uu____9789 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____9789 in
                             (match uu____9781 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____9810 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_57  ->
                                         FStar_TypeChecker_Common.TProb _0_57)
                                      uu____9810 in
                                  let uu____9815 =
                                    let uu____9818 =
                                      let uu____9819 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____9819.FStar_Syntax_Syntax.n in
                                    let uu____9822 =
                                      let uu____9823 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____9823.FStar_Syntax_Syntax.n in
                                    (uu____9818, uu____9822) in
                                  (match uu____9815 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____9831,uu____9832) ->
                                       (k1', [sub_prob])
                                   | (uu____9836,FStar_Syntax_Syntax.Tm_type
                                      uu____9837) -> (k2', [sub_prob])
                                   | uu____9841 ->
                                       let uu____9844 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____9844 with
                                        | (t,uu____9853) ->
                                            let uu____9854 = new_uvar r zs t in
                                            (match uu____9854 with
                                             | (k_zs,uu____9863) ->
                                                 let kprob =
                                                   let uu____9865 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_58  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_58) uu____9865 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____9749 with
                       | (k_u',sub_probs) ->
                           let uu____9879 =
                             let uu____9887 =
                               let uu____9888 = new_uvar r zs k_u' in
                               FStar_All.pipe_left Prims.fst uu____9888 in
                             let uu____9893 =
                               let uu____9896 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____9896 in
                             let uu____9899 =
                               let uu____9902 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____9902 in
                             (uu____9887, uu____9893, uu____9899) in
                           (match uu____9879 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____9921 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____9921 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____9945 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____9945
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____9952 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____9952 with
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
             let solve_one_pat uu____10004 uu____10005 =
               match (uu____10004, uu____10005) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10109 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10109
                     then
                       let uu____10110 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10111 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10110 uu____10111
                     else ());
                    (let uu____10113 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____10113
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10123  ->
                              fun uu____10124  ->
                                match (uu____10123, uu____10124) with
                                | ((a,uu____10134),(t21,uu____10136)) ->
                                    let uu____10141 =
                                      let uu____10144 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10144
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10141
                                      (fun _0_59  ->
                                         FStar_TypeChecker_Common.TProb _0_59))
                           xs args2 in
                       let guard =
                         let uu____10148 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p) Prims.fst)
                             sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10148 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10158 = occurs_check env wl (u1, k1) t21 in
                        match uu____10158 with
                        | (occurs_ok,uu____10167) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10172 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10172
                            then
                              let sol =
                                let uu____10174 =
                                  let uu____10179 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10179) in
                                TERM uu____10174 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10192 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10192
                               then
                                 let uu____10193 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10193 with
                                 | (sol,(uu____10207,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10217 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10217
                                       then
                                         let uu____10218 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10218
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10223 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10225 = lhs in
             match uu____10225 with
             | (t1,u1,k1,args1) ->
                 let uu____10230 = rhs in
                 (match uu____10230 with
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
                       | uu____10256 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10262 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10262 with
                              | (sol,uu____10269) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10272 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10272
                                    then
                                      let uu____10273 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10273
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10278 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10280 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10280
        then
          let uu____10281 = solve_prob orig None [] wl in
          solve env uu____10281
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10285 = FStar_Util.physical_equality t1 t2 in
           if uu____10285
           then
             let uu____10286 = solve_prob orig None [] wl in
             solve env uu____10286
           else
             ((let uu____10289 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10289
               then
                 let uu____10290 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10290
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
                   let mk_c c uu___129_10336 =
                     match uu___129_10336 with
                     | [] -> c
                     | bs ->
                         let uu____10350 =
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10350 in
                   let uu____10364 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10364 with
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
                                   let uu____10450 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____10450
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____10452 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_TypeChecker_Common.CProb _0_60)
                                   uu____10452))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___130_10529 =
                     match uu___130_10529 with
                     | [] -> t
                     | bs ->
                         (FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____10568 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____10568 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10651 =
                                   let uu____10654 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____10655 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____10654
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10655 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____10651))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10670 -> true
                     | uu____10685 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____10713 =
                     let uu____10724 = maybe_eta t1 in
                     let uu____10729 = maybe_eta t2 in
                     (uu____10724, uu____10729) in
                   (match uu____10713 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___163_10760 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___163_10760.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___163_10760.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___163_10760.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___163_10760.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___163_10760.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___163_10760.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___163_10760.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___163_10760.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10793 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____10793
                        then
                          let uu____10794 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____10794 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10799 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____10810,FStar_Syntax_Syntax.Tm_refine uu____10811) ->
                   let uu____10820 = as_refinement env wl t1 in
                   (match uu____10820 with
                    | (x1,phi1) ->
                        let uu____10825 = as_refinement env wl t2 in
                        (match uu____10825 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____10831 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_62  ->
                                    FStar_TypeChecker_Common.TProb _0_62)
                                 uu____10831 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____10864 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____10864
                                 (guard_on_element wl problem x11) in
                             let fallback uu____10868 =
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
                                 let uu____10874 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst in
                                 FStar_Syntax_Util.mk_conj uu____10874 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____10881 =
                                   let uu____10884 =
                                     let uu____10885 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____10885 :: (p_scope orig) in
                                   mk_problem uu____10884 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_TypeChecker_Common.TProb _0_63)
                                   uu____10881 in
                               let uu____10888 =
                                 solve env1
                                   (let uu___164_10889 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___164_10889.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___164_10889.smt_ok);
                                      tcenv = (uu___164_10889.tcenv)
                                    }) in
                               (match uu____10888 with
                                | Failed uu____10893 -> fallback ()
                                | Success uu____10896 ->
                                    let guard =
                                      let uu____10900 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob) Prims.fst in
                                      let uu____10903 =
                                        let uu____10904 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob) Prims.fst in
                                        FStar_All.pipe_right uu____10904
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____10900
                                        uu____10903 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___165_10911 = wl1 in
                                      {
                                        attempting =
                                          (uu___165_10911.attempting);
                                        wl_deferred =
                                          (uu___165_10911.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___165_10911.defer_ok);
                                        smt_ok = (uu___165_10911.smt_ok);
                                        tcenv = (uu___165_10911.tcenv)
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
                   let uu____10965 = destruct_flex_t t1 in
                   let uu____10966 = destruct_flex_t t2 in
                   flex_flex1 orig uu____10965 uu____10966
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
                   let uu____10982 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____10982 t2 wl
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
                     (let uu___166_11031 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___166_11031.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___166_11031.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___166_11031.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___166_11031.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___166_11031.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___166_11031.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___166_11031.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___166_11031.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___166_11031.FStar_TypeChecker_Common.rank)
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
                      let uu____11049 =
                        let uu____11050 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11050 in
                      if uu____11049
                      then
                        let uu____11051 =
                          FStar_All.pipe_left
                            (fun _0_64  ->
                               FStar_TypeChecker_Common.TProb _0_64)
                            (let uu___167_11054 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___167_11054.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___167_11054.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___167_11054.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___167_11054.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___167_11054.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___167_11054.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___167_11054.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___167_11054.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___167_11054.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11055 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11051 uu____11055 t2
                          wl
                      else
                        (let uu____11060 = base_and_refinement env wl t2 in
                         match uu____11060 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____11090 =
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      (let uu___168_11093 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___168_11093.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___168_11093.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___168_11093.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___168_11093.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___168_11093.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___168_11093.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___168_11093.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___168_11093.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___168_11093.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____11094 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____11090
                                    uu____11094 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___169_11109 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___169_11109.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___169_11109.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____11112 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      uu____11112 in
                                  let guard =
                                    let uu____11120 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob) Prims.fst in
                                    FStar_Syntax_Util.mk_conj uu____11120
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
                     (let uu____11142 = base_and_refinement env wl t1 in
                      match uu____11142 with
                      | (t_base,uu____11153) ->
                          solve_t env
                            (let uu___170_11168 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_11168.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_11168.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_11168.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_11168.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_11168.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_11168.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_11168.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_11168.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____11171,uu____11172) ->
                   let t21 =
                     let uu____11180 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____11180 in
                   solve_t env
                     (let uu___171_11193 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___171_11193.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___171_11193.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___171_11193.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___171_11193.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___171_11193.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___171_11193.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___171_11193.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___171_11193.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___171_11193.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11194,FStar_Syntax_Syntax.Tm_refine uu____11195) ->
                   let t11 =
                     let uu____11203 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____11203 in
                   solve_t env
                     (let uu___172_11216 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_11216.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___172_11216.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___172_11216.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___172_11216.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_11216.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_11216.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_11216.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_11216.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_11216.FStar_TypeChecker_Common.rank)
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
                     let uu____11246 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11246 Prims.fst in
                   let head2 =
                     let uu____11277 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11277 Prims.fst in
                   let uu____11305 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11305
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11314 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11314
                      then
                        let guard =
                          let uu____11321 =
                            let uu____11322 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____11322 = FStar_Syntax_Util.Equal in
                          if uu____11321
                          then None
                          else
                            (let uu____11325 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_67  -> Some _0_67)
                               uu____11325) in
                        let uu____11327 = solve_prob orig guard [] wl in
                        solve env uu____11327
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____11331,uu____11332),uu____11333) ->
                   solve_t' env
                     (let uu___173_11362 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_11362.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_11362.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_11362.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_11362.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_11362.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_11362.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_11362.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_11362.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_11362.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11365,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____11367,uu____11368)) ->
                   solve_t' env
                     (let uu___174_11397 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_11397.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_11397.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_11397.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_11397.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_11397.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_11397.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_11397.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_11397.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_11397.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   let uu____11410 =
                     let uu____11411 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____11412 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____11411
                       uu____11412 in
                   failwith uu____11410
               | uu____11413 -> giveup env "head tag mismatch" orig)))
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
          (let uu____11445 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____11445
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____11453  ->
                  fun uu____11454  ->
                    match (uu____11453, uu____11454) with
                    | ((a1,uu____11464),(a2,uu____11466)) ->
                        let uu____11471 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                          uu____11471)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____11477 =
               FStar_List.map
                 (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____11477 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____11497 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____11504)::[] -> wp1
              | uu____11517 ->
                  let uu____11523 =
                    let uu____11524 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____11524 in
                  failwith uu____11523 in
            let uu____11527 =
              let uu____11533 =
                let uu____11534 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____11534 in
              [uu____11533] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____11527;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____11535 = lift_c1 () in solve_eq uu____11535 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___131_11539  ->
                       match uu___131_11539 with
                       | FStar_Syntax_Syntax.TOTAL 
                         |FStar_Syntax_Syntax.MLEFFECT 
                          |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____11540 -> false)) in
             let uu____11541 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____11565)::uu____11566,(wp2,uu____11568)::uu____11569)
                   -> (wp1, wp2)
               | uu____11610 ->
                   let uu____11623 =
                     let uu____11624 =
                       let uu____11627 =
                         let uu____11628 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____11629 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____11628 uu____11629 in
                       (uu____11627, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____11624 in
                   Prims.raise uu____11623 in
             match uu____11541 with
             | (wpc1,wpc2) ->
                 let uu____11646 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____11646
                 then
                   let uu____11649 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____11649 wl
                 else
                   (let c2_decl =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c21.FStar_Syntax_Syntax.effect_name in
                    let uu____11654 =
                      FStar_All.pipe_right
                        c2_decl.FStar_Syntax_Syntax.qualifiers
                        (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                    if uu____11654
                    then
                      let c1_repr =
                        let uu____11657 =
                          let uu____11658 =
                            let uu____11659 = lift_c1 () in
                            FStar_Syntax_Syntax.mk_Comp uu____11659 in
                          let uu____11660 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c11.FStar_Syntax_Syntax.result_typ in
                          FStar_TypeChecker_Env.reify_comp env uu____11658
                            uu____11660 in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11657 in
                      let c2_repr =
                        let uu____11662 =
                          let uu____11663 = FStar_Syntax_Syntax.mk_Comp c21 in
                          let uu____11664 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c21.FStar_Syntax_Syntax.result_typ in
                          FStar_TypeChecker_Env.reify_comp env uu____11663
                            uu____11664 in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11662 in
                      let prob =
                        let uu____11666 =
                          let uu____11669 =
                            let uu____11670 =
                              FStar_Syntax_Print.term_to_string c1_repr in
                            let uu____11671 =
                              FStar_Syntax_Print.term_to_string c2_repr in
                            FStar_Util.format2 "sub effect repr: %s <: %s"
                              uu____11670 uu____11671 in
                          sub_prob c1_repr
                            problem.FStar_TypeChecker_Common.relation c2_repr
                            uu____11669 in
                        FStar_TypeChecker_Common.TProb uu____11666 in
                      let wl1 =
                        let uu____11673 =
                          let uu____11675 =
                            FStar_All.pipe_right (p_guard prob) Prims.fst in
                          Some uu____11675 in
                        solve_prob orig uu____11673 [] wl in
                      solve env (attempt [prob] wl1)
                    else
                      (let g =
                         if env.FStar_TypeChecker_Env.lax
                         then FStar_Syntax_Util.t_true
                         else
                           if is_null_wp_2
                           then
                             ((let uu____11682 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Rel") in
                               if uu____11682
                               then
                                 FStar_Util.print_string
                                   "Using trivial wp ... \n"
                               else ());
                              (let uu____11684 =
                                 let uu____11687 =
                                   let uu____11688 =
                                     let uu____11698 =
                                       let uu____11699 =
                                         let uu____11700 =
                                           env.FStar_TypeChecker_Env.universe_of
                                             env
                                             c11.FStar_Syntax_Syntax.result_typ in
                                         [uu____11700] in
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         uu____11699 env c2_decl
                                         c2_decl.FStar_Syntax_Syntax.trivial in
                                     let uu____11701 =
                                       let uu____11703 =
                                         FStar_Syntax_Syntax.as_arg
                                           c11.FStar_Syntax_Syntax.result_typ in
                                       let uu____11704 =
                                         let uu____11706 =
                                           let uu____11707 =
                                             (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                               c11.FStar_Syntax_Syntax.result_typ
                                               wpc1 in
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             uu____11707 in
                                         [uu____11706] in
                                       uu____11703 :: uu____11704 in
                                     (uu____11698, uu____11701) in
                                   FStar_Syntax_Syntax.Tm_app uu____11688 in
                                 FStar_Syntax_Syntax.mk uu____11687 in
                               uu____11684
                                 (Some
                                    (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                 r))
                           else
                             (let uu____11718 =
                                let uu____11721 =
                                  let uu____11722 =
                                    let uu____11732 =
                                      let uu____11733 =
                                        let uu____11734 =
                                          env.FStar_TypeChecker_Env.universe_of
                                            env
                                            c21.FStar_Syntax_Syntax.result_typ in
                                        [uu____11734] in
                                      FStar_TypeChecker_Env.inst_effect_fun_with
                                        uu____11733 env c2_decl
                                        c2_decl.FStar_Syntax_Syntax.stronger in
                                    let uu____11735 =
                                      let uu____11737 =
                                        FStar_Syntax_Syntax.as_arg
                                          c21.FStar_Syntax_Syntax.result_typ in
                                      let uu____11738 =
                                        let uu____11740 =
                                          FStar_Syntax_Syntax.as_arg wpc2 in
                                        let uu____11741 =
                                          let uu____11743 =
                                            let uu____11744 =
                                              (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                c11.FStar_Syntax_Syntax.result_typ
                                                wpc1 in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____11744 in
                                          [uu____11743] in
                                        uu____11740 :: uu____11741 in
                                      uu____11737 :: uu____11738 in
                                    (uu____11732, uu____11735) in
                                  FStar_Syntax_Syntax.Tm_app uu____11722 in
                                FStar_Syntax_Syntax.mk uu____11721 in
                              uu____11718
                                (Some
                                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                r) in
                       let base_prob =
                         let uu____11755 =
                           sub_prob c11.FStar_Syntax_Syntax.result_typ
                             problem.FStar_TypeChecker_Common.relation
                             c21.FStar_Syntax_Syntax.result_typ "result type" in
                         FStar_All.pipe_left
                           (fun _0_69  ->
                              FStar_TypeChecker_Common.TProb _0_69)
                           uu____11755 in
                       let wl1 =
                         let uu____11761 =
                           let uu____11763 =
                             let uu____11766 =
                               FStar_All.pipe_right (p_guard base_prob)
                                 Prims.fst in
                             FStar_Syntax_Util.mk_conj uu____11766 g in
                           FStar_All.pipe_left (fun _0_70  -> Some _0_70)
                             uu____11763 in
                         solve_prob orig uu____11761 [] wl in
                       solve env (attempt [base_prob] wl1)))) in
        let uu____11776 = FStar_Util.physical_equality c1 c2 in
        if uu____11776
        then
          let uu____11777 = solve_prob orig None [] wl in
          solve env uu____11777
        else
          ((let uu____11780 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____11780
            then
              let uu____11781 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____11782 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____11781
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____11782
            else ());
           (let uu____11784 =
              let uu____11787 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____11788 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____11787, uu____11788) in
            match uu____11784 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____11792),FStar_Syntax_Syntax.Total
                    (t2,uu____11794)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____11807 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11807 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____11810,FStar_Syntax_Syntax.Total uu____11811) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let uu____11860 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11860 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let uu____11867 =
                       let uu___175_11870 = problem in
                       let uu____11873 =
                         let uu____11874 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11874 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___175_11870.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11873;
                         FStar_TypeChecker_Common.relation =
                           (uu___175_11870.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___175_11870.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___175_11870.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___175_11870.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___175_11870.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___175_11870.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___175_11870.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___175_11870.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11867 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let uu____11879 =
                       let uu___176_11882 = problem in
                       let uu____11885 =
                         let uu____11886 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11886 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_11882.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___176_11882.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___176_11882.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11885;
                         FStar_TypeChecker_Common.element =
                           (uu___176_11882.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_11882.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_11882.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_11882.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_11882.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_11882.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11879 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____11887,FStar_Syntax_Syntax.Comp uu____11888) ->
                     let uu____11889 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____11889
                     then
                       let uu____11890 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____11890 wl
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
                           (let uu____11900 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____11900
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____11902 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____11902 with
                            | None  ->
                                let uu____11904 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____11905 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____11905) in
                                if uu____11904
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
                                  (let uu____11908 =
                                     let uu____11909 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____11910 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____11909 uu____11910 in
                                   giveup env uu____11908 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11915 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____11935  ->
              match uu____11935 with
              | (uu____11946,uu____11947,u,uu____11949,uu____11950,uu____11951)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____11915 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11980 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____11980 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____11990 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____12002  ->
                match uu____12002 with
                | (u1,u2) ->
                    let uu____12007 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____12008 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____12007 uu____12008)) in
      FStar_All.pipe_right uu____11990 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____12020,[])) -> "{}"
      | uu____12033 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____12043 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____12043
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____12046 =
              FStar_List.map
                (fun uu____12050  ->
                   match uu____12050 with
                   | (uu____12053,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____12046 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____12057 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____12057 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____12095 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____12095
    then
      let uu____12096 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____12097 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____12096
        (rel_to_string rel) uu____12097
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
            let uu____12117 =
              let uu____12119 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_71  -> Some _0_71) uu____12119 in
            FStar_Syntax_Syntax.new_bv uu____12117 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____12125 =
              let uu____12127 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_72  -> Some _0_72) uu____12127 in
            let uu____12129 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____12125 uu____12129 in
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
          let uu____12152 = FStar_Options.eager_inference () in
          if uu____12152
          then
            let uu___177_12153 = probs in
            {
              attempting = (uu___177_12153.attempting);
              wl_deferred = (uu___177_12153.wl_deferred);
              ctr = (uu___177_12153.ctr);
              defer_ok = false;
              smt_ok = (uu___177_12153.smt_ok);
              tcenv = (uu___177_12153.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____12164 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____12164
              then
                let uu____12165 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____12165
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
          ((let uu____12175 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____12175
            then
              let uu____12176 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____12176
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____12180 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____12180
             then
               let uu____12181 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____12181
             else ());
            (let f2 =
               let uu____12184 =
                 let uu____12185 = FStar_Syntax_Util.unmeta f1 in
                 uu____12185.FStar_Syntax_Syntax.n in
               match uu____12184 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____12189 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___178_12190 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___178_12190.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___178_12190.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___178_12190.FStar_TypeChecker_Env.implicits)
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
            let uu____12205 =
              let uu____12206 =
                let uu____12207 =
                  let uu____12208 =
                    FStar_All.pipe_right (p_guard prob) Prims.fst in
                  FStar_All.pipe_right uu____12208
                    (fun _0_73  -> FStar_TypeChecker_Common.NonTrivial _0_73) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____12207;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____12206 in
            FStar_All.pipe_left (fun _0_74  -> Some _0_74) uu____12205
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
          (let uu____12235 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12235
           then
             let uu____12236 = FStar_Syntax_Print.term_to_string t1 in
             let uu____12237 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____12236
               uu____12237
           else ());
          (let prob =
             let uu____12240 =
               let uu____12243 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____12243 in
             FStar_All.pipe_left
               (fun _0_75  -> FStar_TypeChecker_Common.TProb _0_75)
               uu____12240 in
           let g =
             let uu____12248 =
               let uu____12250 = singleton' env prob smt_ok in
               solve_and_commit env uu____12250 (fun uu____12251  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____12248 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12265 = try_teq true env t1 t2 in
        match uu____12265 with
        | None  ->
            let uu____12267 =
              let uu____12268 =
                let uu____12271 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____12272 = FStar_TypeChecker_Env.get_range env in
                (uu____12271, uu____12272) in
              FStar_Errors.Error uu____12268 in
            Prims.raise uu____12267
        | Some g ->
            ((let uu____12275 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____12275
              then
                let uu____12276 = FStar_Syntax_Print.term_to_string t1 in
                let uu____12277 = FStar_Syntax_Print.term_to_string t2 in
                let uu____12278 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____12276
                  uu____12277 uu____12278
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
          (let uu____12294 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12294
           then
             let uu____12295 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____12296 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____12295
               uu____12296
           else ());
          (let uu____12298 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____12298 with
           | (prob,x) ->
               let g =
                 let uu____12306 =
                   let uu____12308 = singleton' env prob smt_ok in
                   solve_and_commit env uu____12308
                     (fun uu____12309  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____12306 in
               ((let uu____12315 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____12315
                 then
                   let uu____12316 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____12317 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____12318 =
                     let uu____12319 = FStar_Util.must g in
                     guard_to_string env uu____12319 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____12316 uu____12317 uu____12318
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
          let uu____12343 = FStar_TypeChecker_Env.get_range env in
          let uu____12344 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____12343 uu____12344
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____12356 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____12356
         then
           let uu____12357 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____12358 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____12357
             uu____12358
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____12363 =
             let uu____12366 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____12366 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_76  -> FStar_TypeChecker_Common.CProb _0_76) uu____12363 in
         let uu____12369 =
           let uu____12371 = singleton env prob in
           solve_and_commit env uu____12371 (fun uu____12372  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____12369)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____12391  ->
        match uu____12391 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____12416 =
                 let uu____12417 =
                   let uu____12420 =
                     let uu____12421 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____12422 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____12421 uu____12422 in
                   let uu____12423 = FStar_TypeChecker_Env.get_range env in
                   (uu____12420, uu____12423) in
                 FStar_Errors.Error uu____12417 in
               Prims.raise uu____12416) in
            let equiv v1 v' =
              let uu____12431 =
                let uu____12434 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____12435 = FStar_Syntax_Subst.compress_univ v' in
                (uu____12434, uu____12435) in
              match uu____12431 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____12443 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____12457 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____12457 with
                      | FStar_Syntax_Syntax.U_unif uu____12461 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____12472  ->
                                    match uu____12472 with
                                    | (u,v') ->
                                        let uu____12478 = equiv v1 v' in
                                        if uu____12478
                                        then
                                          let uu____12480 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____12480 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____12490 -> [])) in
            let uu____12493 =
              let wl =
                let uu___179_12496 = empty_worklist env in
                {
                  attempting = (uu___179_12496.attempting);
                  wl_deferred = (uu___179_12496.wl_deferred);
                  ctr = (uu___179_12496.ctr);
                  defer_ok = false;
                  smt_ok = (uu___179_12496.smt_ok);
                  tcenv = (uu___179_12496.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____12503  ->
                      match uu____12503 with
                      | (lb,v1) ->
                          let uu____12508 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____12508 with
                           | USolved wl1 -> ()
                           | uu____12510 -> fail lb v1))) in
            let rec check_ineq uu____12516 =
              match uu____12516 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____12523) -> true
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
                   | (FStar_Syntax_Syntax.U_max us,uu____12539) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12543,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____12548 -> false) in
            let uu____12551 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____12557  ->
                      match uu____12557 with
                      | (u,v1) ->
                          let uu____12562 = check_ineq (u, v1) in
                          if uu____12562
                          then true
                          else
                            ((let uu____12565 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____12565
                              then
                                let uu____12566 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____12567 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____12566
                                  uu____12567
                              else ());
                             false))) in
            if uu____12551
            then ()
            else
              ((let uu____12571 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____12571
                then
                  ((let uu____12573 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____12573);
                   FStar_Unionfind.rollback tx;
                   (let uu____12579 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____12579))
                else ());
               (let uu____12585 =
                  let uu____12586 =
                    let uu____12589 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____12589) in
                  FStar_Errors.Error uu____12586 in
                Prims.raise uu____12585))
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
      let fail uu____12622 =
        match uu____12622 with
        | (d,s) ->
            let msg = explain env d s in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____12632 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____12632
       then
         let uu____12633 = wl_to_string wl in
         let uu____12634 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____12633 uu____12634
       else ());
      (let g1 =
         let uu____12646 = solve_and_commit env wl fail in
         match uu____12646 with
         | Some [] ->
             let uu___180_12653 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___180_12653.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_12653.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_12653.FStar_TypeChecker_Env.implicits)
             }
         | uu____12656 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___181_12659 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___181_12659.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___181_12659.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___181_12659.FStar_TypeChecker_Env.implicits)
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
            let uu___182_12685 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___182_12685.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___182_12685.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___182_12685.FStar_TypeChecker_Env.implicits)
            } in
          let uu____12686 =
            let uu____12687 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____12687 in
          if uu____12686
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____12693 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Norm") in
                   if uu____12693
                   then
                     let uu____12694 = FStar_TypeChecker_Env.get_range env in
                     let uu____12695 =
                       let uu____12696 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____12696 in
                     FStar_Errors.diag uu____12694 uu____12695
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
                         ((let uu____12705 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____12705
                           then
                             let uu____12706 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____12707 =
                               let uu____12708 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____12708 in
                             FStar_Errors.diag uu____12706 uu____12707
                           else ());
                          (let vcs =
                             let uu____12714 = FStar_Options.use_tactics () in
                             if uu____12714
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____12728  ->
                                   match uu____12728 with
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
      let uu____12739 = discharge_guard' None env g true in
      match uu____12739 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____12759 = FStar_Unionfind.find u in
      match uu____12759 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____12768 -> false in
    let rec until_fixpoint acc implicits =
      let uu____12783 = acc in
      match uu____12783 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____12829 = hd1 in
               (match uu____12829 with
                | (uu____12836,env,u,tm,k,r) ->
                    let uu____12842 = unresolved u in
                    if uu____12842
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____12860 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____12860
                        then
                          let uu____12861 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____12865 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____12866 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____12861 uu____12865 uu____12866
                        else ());
                       (let uu____12868 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___183_12872 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___183_12872.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___183_12872.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___183_12872.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___183_12872.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___183_12872.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___183_12872.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___183_12872.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___183_12872.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___183_12872.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___183_12872.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___183_12872.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___183_12872.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___183_12872.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___183_12872.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___183_12872.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___183_12872.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___183_12872.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___183_12872.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___183_12872.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___183_12872.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___183_12872.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___183_12872.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___183_12872.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____12868 with
                        | (uu____12873,uu____12874,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___184_12877 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___184_12877.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___184_12877.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___184_12877.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____12880 =
                                discharge_guard'
                                  (Some
                                     (fun uu____12884  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____12880 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___185_12899 = g in
    let uu____12900 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___185_12899.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___185_12899.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___185_12899.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12900
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____12928 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____12928 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____12935 = discharge_guard env g1 in
          FStar_All.pipe_left Prims.ignore uu____12935
      | (reason,uu____12937,uu____12938,e,t,r)::uu____12942 ->
          let uu____12956 =
            let uu____12957 = FStar_Syntax_Print.term_to_string t in
            let uu____12958 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____12957 uu____12958 reason in
          FStar_Errors.err r uu____12956
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___186_12965 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___186_12965.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___186_12965.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___186_12965.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12983 = try_teq false env t1 t2 in
        match uu____12983 with
        | None  -> false
        | Some g ->
            let uu____12986 = discharge_guard' None env g false in
            (match uu____12986 with
             | Some uu____12990 -> true
             | None  -> false)