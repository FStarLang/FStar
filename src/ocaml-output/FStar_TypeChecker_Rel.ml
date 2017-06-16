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
            let uu___136_260 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___136_260.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_260.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_260.FStar_TypeChecker_Env.implicits)
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
            let uu___137_287 = g in
            let uu____288 =
              let uu____289 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____289 in
            {
              FStar_TypeChecker_Env.guard_f = uu____288;
              FStar_TypeChecker_Env.deferred =
                (uu___137_287.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_287.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_287.FStar_TypeChecker_Env.implicits)
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
        | uu____330 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____345 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____345 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____361 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____361, uv1)
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
    match projectee with | Success _0 -> true | uu____537 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____551 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____568 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____572 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____576 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_593  ->
    match uu___105_593 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____606 =
    let uu____607 = FStar_Syntax_Subst.compress t in
    uu____607.FStar_Syntax_Syntax.n in
  match uu____606 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____624 = FStar_Syntax_Print.uvar_to_string u in
      let uu____628 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____624 uu____628
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____631;
         FStar_Syntax_Syntax.pos = uu____632;
         FStar_Syntax_Syntax.vars = uu____633;_},args)
      ->
      let uu____661 = FStar_Syntax_Print.uvar_to_string u in
      let uu____665 = FStar_Syntax_Print.term_to_string ty in
      let uu____666 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____661 uu____665 uu____666
  | uu____667 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_673  ->
      match uu___106_673 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____677 =
            let uu____679 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____680 =
              let uu____682 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____683 =
                let uu____685 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____686 =
                  let uu____688 =
                    let uu____690 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____691 =
                      let uu____693 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____694 =
                        let uu____696 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____697 =
                          let uu____699 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____699] in
                        uu____696 :: uu____697 in
                      uu____693 :: uu____694 in
                    uu____690 :: uu____691 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____688 in
                uu____685 :: uu____686 in
              uu____682 :: uu____683 in
            uu____679 :: uu____680 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____677
      | FStar_TypeChecker_Common.CProb p ->
          let uu____704 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____705 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____704
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____705
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_711  ->
      match uu___107_711 with
      | UNIV (u,t) ->
          let x =
            let uu____715 = FStar_Options.hide_uvar_nums () in
            if uu____715
            then "?"
            else
              (let uu____717 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____717 FStar_Util.string_of_int) in
          let uu____719 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____719
      | TERM ((u,uu____721),t) ->
          let x =
            let uu____726 = FStar_Options.hide_uvar_nums () in
            if uu____726
            then "?"
            else
              (let uu____728 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____728 FStar_Util.string_of_int) in
          let uu____732 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____732
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____741 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____741 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____749 =
      let uu____751 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____751
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____749 (FStar_String.concat ", ")
let args_to_string args =
  let uu____769 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____777  ->
            match uu____777 with
            | (x,uu____781) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____769 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____786 =
      let uu____787 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____787 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____786;
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
        let uu___138_800 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___138_800.wl_deferred);
          ctr = (uu___138_800.ctr);
          defer_ok = (uu___138_800.defer_ok);
          smt_ok;
          tcenv = (uu___138_800.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___139_825 = empty_worklist env in
  let uu____826 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____826;
    wl_deferred = (uu___139_825.wl_deferred);
    ctr = (uu___139_825.ctr);
    defer_ok = false;
    smt_ok = (uu___139_825.smt_ok);
    tcenv = (uu___139_825.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_838 = wl in
        {
          attempting = (uu___140_838.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_838.ctr);
          defer_ok = (uu___140_838.defer_ok);
          smt_ok = (uu___140_838.smt_ok);
          tcenv = (uu___140_838.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___141_850 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_850.wl_deferred);
        ctr = (uu___141_850.ctr);
        defer_ok = (uu___141_850.defer_ok);
        smt_ok = (uu___141_850.smt_ok);
        tcenv = (uu___141_850.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____861 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____861
         then
           let uu____862 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____862
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_866  ->
    match uu___108_866 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___142_882 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_882.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_882.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_882.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_882.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_882.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_882.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_882.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_903  ->
    match uu___109_903 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_919  ->
      match uu___110_919 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_922  ->
    match uu___111_922 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_931  ->
    match uu___112_931 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_941  ->
    match uu___113_941 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_951  ->
    match uu___114_951 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___115_962  ->
    match uu___115_962 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_973  ->
    match uu___116_973 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_982  ->
    match uu___117_982 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____996 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____996 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1007  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1057 = next_pid () in
  let uu____1058 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1057;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1058;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1105 = next_pid () in
  let uu____1106 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1105;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1106;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1147 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1147;
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
        let uu____1199 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1199
        then
          let uu____1200 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1201 = prob_to_string env d in
          let uu____1202 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1200 uu____1201 uu____1202 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1207 -> failwith "impossible" in
           let uu____1208 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1216 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1217 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1216, uu____1217)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1221 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1222 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1221, uu____1222) in
           match uu____1208 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1231  ->
            match uu___118_1231 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1238 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1241),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar -> uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1264  ->
           match uu___119_1264 with
           | UNIV uu____1266 -> None
           | TERM ((u,uu____1270),t) ->
               let uu____1274 = FStar_Unionfind.equivalent uv u in
               if uu____1274 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1293  ->
           match uu___120_1293 with
           | UNIV (u',t) ->
               let uu____1297 = FStar_Unionfind.equivalent u u' in
               if uu____1297 then Some t else None
           | uu____1301 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1308 =
        let uu____1309 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1309 in
      FStar_Syntax_Subst.compress uu____1308
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1316 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1316
let norm_arg env t = let uu____1335 = sn env (fst t) in (uu____1335, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1352  ->
              match uu____1352 with
              | (x,imp) ->
                  let uu____1359 =
                    let uu___143_1360 = x in
                    let uu____1361 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1360.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1360.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1361
                    } in
                  (uu____1359, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1376 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1376
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1379 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1379
        | uu____1381 -> u2 in
      let uu____1382 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1382
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1489 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1489 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1501;
               FStar_Syntax_Syntax.pos = uu____1502;
               FStar_Syntax_Syntax.vars = uu____1503;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1524 =
                 let uu____1525 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1526 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1525
                   uu____1526 in
               failwith uu____1524)
    | FStar_Syntax_Syntax.Tm_uinst uu____1536 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1563 =
             let uu____1564 = FStar_Syntax_Subst.compress t1' in
             uu____1564.FStar_Syntax_Syntax.n in
           match uu____1563 with
           | FStar_Syntax_Syntax.Tm_refine uu____1576 -> aux true t1'
           | uu____1581 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1593 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1616 =
             let uu____1617 = FStar_Syntax_Subst.compress t1' in
             uu____1617.FStar_Syntax_Syntax.n in
           match uu____1616 with
           | FStar_Syntax_Syntax.Tm_refine uu____1629 -> aux true t1'
           | uu____1634 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1646 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1678 =
             let uu____1679 = FStar_Syntax_Subst.compress t1' in
             uu____1679.FStar_Syntax_Syntax.n in
           match uu____1678 with
           | FStar_Syntax_Syntax.Tm_refine uu____1691 -> aux true t1'
           | uu____1696 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1708 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1720 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1732 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1744 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1756 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1775 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1801 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1821 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1840 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1867 ->
        let uu____1872 =
          let uu____1873 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1874 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1873
            uu____1874 in
        failwith uu____1872
    | FStar_Syntax_Syntax.Tm_ascribed uu____1884 ->
        let uu____1902 =
          let uu____1903 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1904 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1903
            uu____1904 in
        failwith uu____1902
    | FStar_Syntax_Syntax.Tm_delayed uu____1914 ->
        let uu____1935 =
          let uu____1936 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1937 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1936
            uu____1937 in
        failwith uu____1935
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1947 =
          let uu____1948 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1949 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1948
            uu____1949 in
        failwith uu____1947 in
  let uu____1959 = whnf env t1 in aux false uu____1959
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1968 =
        let uu____1978 = empty_worklist env in
        base_and_refinement env uu____1978 t in
      FStar_All.pipe_right uu____1968 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2002 = FStar_Syntax_Syntax.null_bv t in
    (uu____2002, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2022 = base_and_refinement env wl t in
  match uu____2022 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2081 =
  match uu____2081 with
  | (t_base,refopt) ->
      let uu____2095 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2095 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2119  ->
      match uu___121_2119 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2123 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2124 =
            let uu____2125 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2125 in
          let uu____2126 =
            let uu____2127 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2127 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2123 uu____2124
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2126
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2131 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2132 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2133 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2131 uu____2132
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2133
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2137 =
      let uu____2139 =
        let uu____2141 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2151  ->
                  match uu____2151 with | (uu____2155,uu____2156,x) -> x)) in
        FStar_List.append wl.attempting uu____2141 in
      FStar_List.map (wl_prob_to_string wl) uu____2139 in
    FStar_All.pipe_right uu____2137 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2174 =
          let uu____2184 =
            let uu____2185 = FStar_Syntax_Subst.compress k in
            uu____2185.FStar_Syntax_Syntax.n in
          match uu____2184 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2226 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2226)
              else
                (let uu____2240 = FStar_Syntax_Util.abs_formals t in
                 match uu____2240 with
                 | (ys',t1,uu____2261) ->
                     let uu____2274 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2274))
          | uu____2295 ->
              let uu____2296 =
                let uu____2302 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2302) in
              ((ys, t), uu____2296) in
        match uu____2174 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2357 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2357 c in
               let uu____2359 =
                 let uu____2366 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2366 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2359)
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
            let uu____2417 = p_guard prob in
            match uu____2417 with
            | (uu____2420,uv) ->
                ((let uu____2423 =
                    let uu____2424 = FStar_Syntax_Subst.compress uv in
                    uu____2424.FStar_Syntax_Syntax.n in
                  match uu____2423 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2444 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2444
                        then
                          let uu____2445 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2446 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2447 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2445
                            uu____2446 uu____2447
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2451 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2454 = wl in
                  {
                    attempting = (uu___144_2454.attempting);
                    wl_deferred = (uu___144_2454.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2454.defer_ok);
                    smt_ok = (uu___144_2454.smt_ok);
                    tcenv = (uu___144_2454.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2467 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2467
         then
           let uu____2468 = FStar_Util.string_of_int pid in
           let uu____2469 =
             let uu____2470 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2470 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2468 uu____2469
         else ());
        commit sol;
        (let uu___145_2475 = wl in
         {
           attempting = (uu___145_2475.attempting);
           wl_deferred = (uu___145_2475.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2475.defer_ok);
           smt_ok = (uu___145_2475.smt_ok);
           tcenv = (uu___145_2475.tcenv)
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
            | (uu____2504,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2512 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2512 in
          (let uu____2518 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2518
           then
             let uu____2519 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2520 =
               let uu____2521 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2521 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2519 uu____2520
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2546 =
    let uu____2550 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2550 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2546
    (FStar_Util.for_some
       (fun uu____2571  ->
          match uu____2571 with
          | (uv,uu____2579) -> FStar_Unionfind.equivalent uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2623 = occurs wl uk t in Prims.op_Negation uu____2623 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2628 =
         let uu____2629 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2633 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2629 uu____2633 in
       Some uu____2628) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2681 = occurs_check env wl uk t in
  match uu____2681 with
  | (occurs_ok,msg) ->
      let uu____2698 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2698, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2762 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2786  ->
            fun uu____2787  ->
              match (uu____2786, uu____2787) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2830 =
                    let uu____2831 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2831 in
                  if uu____2830
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2845 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2845
                     then
                       let uu____2852 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2852)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2762 with | (isect,uu____2874) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2923  ->
          fun uu____2924  ->
            match (uu____2923, uu____2924) with
            | ((a,uu____2934),(b,uu____2936)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2980 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2986  ->
                match uu____2986 with
                | (b,uu____2990) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2980 then None else Some (a, (snd hd1))
  | uu____2999 -> None
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
            let uu____3042 = pat_var_opt env seen hd1 in
            (match uu____3042 with
             | None  ->
                 ((let uu____3050 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3050
                   then
                     let uu____3051 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3051
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3063 =
      let uu____3064 = FStar_Syntax_Subst.compress t in
      uu____3064.FStar_Syntax_Syntax.n in
    match uu____3063 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3067 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3076;
           FStar_Syntax_Syntax.tk = uu____3077;
           FStar_Syntax_Syntax.pos = uu____3078;
           FStar_Syntax_Syntax.vars = uu____3079;_},uu____3080)
        -> true
    | uu____3103 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3165;
         FStar_Syntax_Syntax.pos = uu____3166;
         FStar_Syntax_Syntax.vars = uu____3167;_},args)
      -> (t, uv, k, args)
  | uu____3208 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3262 = destruct_flex_t t in
  match uu____3262 with
  | (t1,uv,k,args) ->
      let uu____3330 = pat_vars env [] args in
      (match uu____3330 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3386 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3435 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3458 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3462 -> false
let head_match: match_result -> match_result =
  fun uu___122_3465  ->
    match uu___122_3465 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3474 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3487 ->
          let uu____3488 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3488 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3498 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3512 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3518 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3540 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3541 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3542 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3551 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3559 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3576) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3582,uu____3583) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3613) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3628;
             FStar_Syntax_Syntax.index = uu____3629;
             FStar_Syntax_Syntax.sort = t2;_},uu____3631)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3638 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3639 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3640 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3648 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3664 = fv_delta_depth env fv in Some uu____3664
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
            let uu____3683 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3683
            then FullMatch
            else
              (let uu____3685 =
                 let uu____3690 =
                   let uu____3692 = fv_delta_depth env f in Some uu____3692 in
                 let uu____3693 =
                   let uu____3695 = fv_delta_depth env g in Some uu____3695 in
                 (uu____3690, uu____3693) in
               MisMatch uu____3685)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3699),FStar_Syntax_Syntax.Tm_uinst (g,uu____3701)) ->
            let uu____3710 = head_matches env f g in
            FStar_All.pipe_right uu____3710 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3717),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3719)) ->
            let uu____3744 = FStar_Unionfind.equivalent uv uv' in
            if uu____3744 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3752),FStar_Syntax_Syntax.Tm_refine (y,uu____3754)) ->
            let uu____3763 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3763 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3765),uu____3766) ->
            let uu____3771 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3771 head_match
        | (uu____3772,FStar_Syntax_Syntax.Tm_refine (x,uu____3774)) ->
            let uu____3779 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3779 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3780,FStar_Syntax_Syntax.Tm_type
           uu____3781) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3782,FStar_Syntax_Syntax.Tm_arrow uu____3783) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3799),FStar_Syntax_Syntax.Tm_app (head',uu____3801))
            ->
            let uu____3830 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3830 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3832),uu____3833) ->
            let uu____3848 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3848 head_match
        | (uu____3849,FStar_Syntax_Syntax.Tm_app (head1,uu____3851)) ->
            let uu____3866 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3866 head_match
        | uu____3867 ->
            let uu____3870 =
              let uu____3875 = delta_depth_of_term env t11 in
              let uu____3877 = delta_depth_of_term env t21 in
              (uu____3875, uu____3877) in
            MisMatch uu____3870
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3913 = FStar_Syntax_Util.head_and_args t in
    match uu____3913 with
    | (head1,uu____3925) ->
        let uu____3940 =
          let uu____3941 = FStar_Syntax_Util.un_uinst head1 in
          uu____3941.FStar_Syntax_Syntax.n in
        (match uu____3940 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3946 =
               let uu____3947 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3947 FStar_Option.isSome in
             if uu____3946
             then
               let uu____3961 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3961 (fun _0_38  -> Some _0_38)
             else None
         | uu____3964 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4032) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4042 =
             let uu____4047 = maybe_inline t11 in
             let uu____4049 = maybe_inline t21 in (uu____4047, uu____4049) in
           match uu____4042 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4070,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4080 =
             let uu____4085 = maybe_inline t11 in
             let uu____4087 = maybe_inline t21 in (uu____4085, uu____4087) in
           match uu____4080 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4112 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4112 with
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
        let uu____4127 =
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
             let uu____4135 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4135)) in
        (match uu____4127 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4143 -> fail r
    | uu____4148 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4177 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4207 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4222 = FStar_Syntax_Util.type_u () in
      match uu____4222 with
      | (t,uu____4226) ->
          let uu____4227 = new_uvar r binders t in fst uu____4227
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4236 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4236 FStar_Pervasives.fst
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
        let uu____4278 = head_matches env t1 t' in
        match uu____4278 with
        | MisMatch uu____4279 -> false
        | uu____4284 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4344,imp),T (t2,uu____4347)) -> (t2, imp)
                     | uu____4364 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4404  ->
                    match uu____4404 with
                    | (t2,uu____4412) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4442 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4442 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4495))::tcs2) ->
                       aux
                         (((let uu___146_4517 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4517.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4517.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4527 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_4558 =
                 match uu___123_4558 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4621 = decompose1 [] bs1 in
               (rebuild, matches, uu____4621))
      | uu____4649 ->
          let rebuild uu___124_4654 =
            match uu___124_4654 with
            | [] -> t1
            | uu____4656 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4675  ->
    match uu___125_4675 with
    | T (t,uu____4677) -> t
    | uu____4686 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4689  ->
    match uu___126_4689 with
    | T (t,uu____4691) -> FStar_Syntax_Syntax.as_arg t
    | uu____4700 -> failwith "Impossible"
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
              | (uu____4769,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4788 = new_uvar r scope1 k in
                  (match uu____4788 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4800 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4815 =
                         let uu____4816 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4816 in
                       ((T (gi_xs, mk_kind)), uu____4815))
              | (uu____4825,uu____4826,C uu____4827) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4914 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4925;
                         FStar_Syntax_Syntax.pos = uu____4926;
                         FStar_Syntax_Syntax.vars = uu____4927;_})
                        ->
                        let uu____4942 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4942 with
                         | (T (gi_xs,uu____4958),prob) ->
                             let uu____4968 =
                               let uu____4969 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4969 in
                             (uu____4968, [prob])
                         | uu____4971 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4981;
                         FStar_Syntax_Syntax.pos = uu____4982;
                         FStar_Syntax_Syntax.vars = uu____4983;_})
                        ->
                        let uu____4998 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4998 with
                         | (T (gi_xs,uu____5014),prob) ->
                             let uu____5024 =
                               let uu____5025 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5025 in
                             (uu____5024, [prob])
                         | uu____5027 -> failwith "impossible")
                    | (uu____5033,uu____5034,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5036;
                         FStar_Syntax_Syntax.pos = uu____5037;
                         FStar_Syntax_Syntax.vars = uu____5038;_})
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
                        let uu____5112 =
                          let uu____5117 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5117 FStar_List.unzip in
                        (match uu____5112 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5146 =
                                 let uu____5147 =
                                   let uu____5150 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5150 un_T in
                                 let uu____5151 =
                                   let uu____5157 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5157
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5147;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5151;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5146 in
                             ((C gi_xs), sub_probs))
                    | uu____5162 ->
                        let uu____5169 = sub_prob scope1 args q in
                        (match uu____5169 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4914 with
                   | (tc,probs) ->
                       let uu____5187 =
                         match q with
                         | (Some b,uu____5213,uu____5214) ->
                             let uu____5222 =
                               let uu____5226 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5226 :: args in
                             ((Some b), (b :: scope1), uu____5222)
                         | uu____5244 -> (None, scope1, args) in
                       (match uu____5187 with
                        | (bopt,scope2,args1) ->
                            let uu____5287 = aux scope2 args1 qs2 in
                            (match uu____5287 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5308 =
                                         let uu____5310 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5310 in
                                       FStar_Syntax_Util.mk_conj_l uu____5308
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5323 =
                                         let uu____5325 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5326 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5325 :: uu____5326 in
                                       FStar_Syntax_Util.mk_conj_l uu____5323 in
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
  let uu___147_5379 = p in
  let uu____5382 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5383 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5379.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5382;
    FStar_TypeChecker_Common.relation =
      (uu___147_5379.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5383;
    FStar_TypeChecker_Common.element =
      (uu___147_5379.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5379.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5379.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5379.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5379.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5379.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5393 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5393
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5398 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5412 = compress_prob wl pr in
        FStar_All.pipe_right uu____5412 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5418 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5418 with
           | (lh,uu____5431) ->
               let uu____5446 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5446 with
                | (rh,uu____5459) ->
                    let uu____5474 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5483,FStar_Syntax_Syntax.Tm_uvar uu____5484)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5503,uu____5504)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5515,FStar_Syntax_Syntax.Tm_uvar uu____5516)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5527,uu____5528)
                          ->
                          let uu____5537 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5537 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5577 ->
                                    let rank =
                                      let uu____5584 = is_top_level_prob prob in
                                      if uu____5584
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5586 =
                                      let uu___148_5589 = tp in
                                      let uu____5592 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5589.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5589.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5589.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5592;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5589.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5589.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5589.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5589.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5589.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5589.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5586)))
                      | (uu____5602,FStar_Syntax_Syntax.Tm_uvar uu____5603)
                          ->
                          let uu____5612 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5612 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5652 ->
                                    let uu____5658 =
                                      let uu___149_5663 = tp in
                                      let uu____5666 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5663.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5666;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5663.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5663.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5663.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5663.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5663.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5663.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5663.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5663.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5658)))
                      | (uu____5682,uu____5683) -> (rigid_rigid, tp) in
                    (match uu____5474 with
                     | (rank,tp1) ->
                         let uu____5694 =
                           FStar_All.pipe_right
                             (let uu___150_5697 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5697.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5697.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5697.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5697.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5697.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5697.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5697.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5697.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5697.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5694))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5703 =
            FStar_All.pipe_right
              (let uu___151_5706 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5706.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5706.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5706.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5706.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5706.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5706.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5706.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5706.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5706.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5703)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5738 probs =
      match uu____5738 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5768 = rank wl hd1 in
               (match uu____5768 with
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
    match projectee with | UDeferred _0 -> true | uu____5836 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5848 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5860 -> false
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
                        let uu____5897 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5897 with
                        | (k,uu____5901) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5906 -> false)))
            | uu____5907 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5950 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5950 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5953 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5959 =
                     let uu____5960 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5961 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5960
                       uu____5961 in
                   UFailed uu____5959)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5977 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5977 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5995 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5995 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5998 ->
                let uu____6001 =
                  let uu____6002 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____6003 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6002
                    uu____6003 msg in
                UFailed uu____6001 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6004,uu____6005) ->
              let uu____6006 =
                let uu____6007 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6008 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6007 uu____6008 in
              failwith uu____6006
          | (FStar_Syntax_Syntax.U_unknown ,uu____6009) ->
              let uu____6010 =
                let uu____6011 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6012 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6011 uu____6012 in
              failwith uu____6010
          | (uu____6013,FStar_Syntax_Syntax.U_bvar uu____6014) ->
              let uu____6015 =
                let uu____6016 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6017 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6016 uu____6017 in
              failwith uu____6015
          | (uu____6018,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6019 =
                let uu____6020 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6021 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6020 uu____6021 in
              failwith uu____6019
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6033 = FStar_Unionfind.equivalent v1 v2 in
              if uu____6033
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6044 = occurs_univ v1 u3 in
              if uu____6044
              then
                let uu____6045 =
                  let uu____6046 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6047 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6046 uu____6047 in
                try_umax_components u11 u21 uu____6045
              else
                (let uu____6049 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6049)
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
          | (FStar_Syntax_Syntax.U_max uu____6065,uu____6066) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6071 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6071
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6073,FStar_Syntax_Syntax.U_max uu____6074) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6079 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6079
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6081,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6082,FStar_Syntax_Syntax.U_name
             uu____6083) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6084) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6085) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6086,FStar_Syntax_Syntax.U_succ
             uu____6087) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6088,FStar_Syntax_Syntax.U_zero
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
  let uu____6150 = bc1 in
  match uu____6150 with
  | (bs1,mk_cod1) ->
      let uu____6175 = bc2 in
      (match uu____6175 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6222 = FStar_Util.first_N n1 bs in
             match uu____6222 with
             | (bs3,rest) ->
                 let uu____6236 = mk_cod rest in (bs3, uu____6236) in
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
               (let uu____6286 = curry l2 bs1 mk_cod1 in
                let uu____6293 =
                  let uu____6297 = mk_cod2 [] in (bs2, uu____6297) in
                (uu____6286, uu____6293))
             else
               (let uu____6306 =
                  let uu____6310 = mk_cod1 [] in (bs1, uu____6310) in
                let uu____6312 = curry l1 bs2 mk_cod2 in
                (uu____6306, uu____6312)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6416 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6416
       then
         let uu____6417 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6417
       else ());
      (let uu____6419 = next_prob probs in
       match uu____6419 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6432 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6432.wl_deferred);
               ctr = (uu___152_6432.ctr);
               defer_ok = (uu___152_6432.defer_ok);
               smt_ok = (uu___152_6432.smt_ok);
               tcenv = (uu___152_6432.tcenv)
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
                  let uu____6439 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6439 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6443 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6443 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6447,uu____6448) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6457 ->
                let uu____6462 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6490  ->
                          match uu____6490 with
                          | (c,uu____6495,uu____6496) -> c < probs.ctr)) in
                (match uu____6462 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6518 =
                            FStar_List.map
                              (fun uu____6524  ->
                                 match uu____6524 with
                                 | (uu____6530,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6518
                      | uu____6533 ->
                          let uu____6538 =
                            let uu___153_6539 = probs in
                            let uu____6540 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6549  ->
                                      match uu____6549 with
                                      | (uu____6553,uu____6554,y) -> y)) in
                            {
                              attempting = uu____6540;
                              wl_deferred = rest;
                              ctr = (uu___153_6539.ctr);
                              defer_ok = (uu___153_6539.defer_ok);
                              smt_ok = (uu___153_6539.smt_ok);
                              tcenv = (uu___153_6539.tcenv)
                            } in
                          solve env uu____6538))))
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
            let uu____6561 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6561 with
            | USolved wl1 ->
                let uu____6563 = solve_prob orig None [] wl1 in
                solve env uu____6563
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
                  let uu____6597 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6597 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6600 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6608;
                  FStar_Syntax_Syntax.pos = uu____6609;
                  FStar_Syntax_Syntax.vars = uu____6610;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6613;
                  FStar_Syntax_Syntax.pos = uu____6614;
                  FStar_Syntax_Syntax.vars = uu____6615;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6627,uu____6628) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6633,FStar_Syntax_Syntax.Tm_uinst uu____6634) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6639 -> USolved wl
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
            ((let uu____6647 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6647
              then
                let uu____6648 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6648 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6656 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6656
         then
           let uu____6657 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6657
         else ());
        (let uu____6659 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6659 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6701 = head_matches_delta env () t1 t2 in
               match uu____6701 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6723 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6749 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6758 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6759 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6758, uu____6759)
                          | None  ->
                              let uu____6762 = FStar_Syntax_Subst.compress t1 in
                              let uu____6763 = FStar_Syntax_Subst.compress t2 in
                              (uu____6762, uu____6763) in
                        (match uu____6749 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6785 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6785 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6808 =
                                    let uu____6814 =
                                      let uu____6817 =
                                        let uu____6820 =
                                          let uu____6821 =
                                            let uu____6826 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6826) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6821 in
                                        FStar_Syntax_Syntax.mk uu____6820 in
                                      uu____6817 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6839 =
                                      let uu____6841 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6841] in
                                    (uu____6814, uu____6839) in
                                  Some uu____6808
                              | (uu____6850,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6852)) ->
                                  let uu____6857 =
                                    let uu____6861 =
                                      let uu____6863 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6863] in
                                    (t11, uu____6861) in
                                  Some uu____6857
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6869),uu____6870) ->
                                  let uu____6875 =
                                    let uu____6879 =
                                      let uu____6881 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6881] in
                                    (t21, uu____6879) in
                                  Some uu____6875
                              | uu____6886 ->
                                  let uu____6889 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6889 with
                                   | (head1,uu____6904) ->
                                       let uu____6919 =
                                         let uu____6920 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6920.FStar_Syntax_Syntax.n in
                                       (match uu____6919 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6927;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6929;_}
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
                                        | uu____6938 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6947) ->
                  let uu____6960 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6969  ->
                            match uu___127_6969 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6974 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6974 with
                                      | (u',uu____6985) ->
                                          let uu____7000 =
                                            let uu____7001 = whnf env u' in
                                            uu____7001.FStar_Syntax_Syntax.n in
                                          (match uu____7000 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7005) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____7021 -> false))
                                 | uu____7022 -> false)
                            | uu____7024 -> false)) in
                  (match uu____6960 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7045 tps =
                         match uu____7045 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7072 =
                                    let uu____7077 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7077 in
                                  (match uu____7072 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7096 -> None) in
                       let uu____7101 =
                         let uu____7106 =
                           let uu____7110 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7110, []) in
                         make_lower_bound uu____7106 lower_bounds in
                       (match uu____7101 with
                        | None  ->
                            ((let uu____7117 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7117
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
                            ((let uu____7130 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7130
                              then
                                let wl' =
                                  let uu___154_7132 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7132.wl_deferred);
                                    ctr = (uu___154_7132.ctr);
                                    defer_ok = (uu___154_7132.defer_ok);
                                    smt_ok = (uu___154_7132.smt_ok);
                                    tcenv = (uu___154_7132.tcenv)
                                  } in
                                let uu____7133 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7133
                              else ());
                             (let uu____7135 =
                                solve_t env eq_prob
                                  (let uu___155_7136 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7136.wl_deferred);
                                     ctr = (uu___155_7136.ctr);
                                     defer_ok = (uu___155_7136.defer_ok);
                                     smt_ok = (uu___155_7136.smt_ok);
                                     tcenv = (uu___155_7136.tcenv)
                                   }) in
                              match uu____7135 with
                              | Success uu____7138 ->
                                  let wl1 =
                                    let uu___156_7140 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7140.wl_deferred);
                                      ctr = (uu___156_7140.ctr);
                                      defer_ok = (uu___156_7140.defer_ok);
                                      smt_ok = (uu___156_7140.smt_ok);
                                      tcenv = (uu___156_7140.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7142 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7145 -> None))))
              | uu____7146 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7153 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7153
         then
           let uu____7154 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7154
         else ());
        (let uu____7156 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7156 with
         | (u,args) ->
             let uu____7183 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7183 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7214 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7214 with
                    | (h1,args1) ->
                        let uu____7242 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7242 with
                         | (h2,uu____7255) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7274 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7274
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7287 =
                                          let uu____7289 =
                                            let uu____7290 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7290 in
                                          [uu____7289] in
                                        Some uu____7287))
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
                                       (let uu____7312 =
                                          let uu____7314 =
                                            let uu____7315 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7315 in
                                          [uu____7314] in
                                        Some uu____7312))
                                  else None
                              | uu____7323 -> None)) in
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
                             let uu____7389 =
                               let uu____7395 =
                                 let uu____7398 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7398 in
                               (uu____7395, m1) in
                             Some uu____7389)
                    | (uu____7407,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7409)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7441),uu____7442) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7473 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7507) ->
                       let uu____7520 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7529  ->
                                 match uu___128_7529 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7534 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7534 with
                                           | (u',uu____7545) ->
                                               let uu____7560 =
                                                 let uu____7561 = whnf env u' in
                                                 uu____7561.FStar_Syntax_Syntax.n in
                                               (match uu____7560 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7565) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7581 -> false))
                                      | uu____7582 -> false)
                                 | uu____7584 -> false)) in
                       (match uu____7520 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7609 tps =
                              match uu____7609 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7650 =
                                         let uu____7657 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7657 in
                                       (match uu____7650 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7692 -> None) in
                            let uu____7699 =
                              let uu____7706 =
                                let uu____7712 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7712, []) in
                              make_upper_bound uu____7706 upper_bounds in
                            (match uu____7699 with
                             | None  ->
                                 ((let uu____7721 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7721
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
                                 ((let uu____7740 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7740
                                   then
                                     let wl' =
                                       let uu___157_7742 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7742.wl_deferred);
                                         ctr = (uu___157_7742.ctr);
                                         defer_ok = (uu___157_7742.defer_ok);
                                         smt_ok = (uu___157_7742.smt_ok);
                                         tcenv = (uu___157_7742.tcenv)
                                       } in
                                     let uu____7743 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7743
                                   else ());
                                  (let uu____7745 =
                                     solve_t env eq_prob
                                       (let uu___158_7746 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7746.wl_deferred);
                                          ctr = (uu___158_7746.ctr);
                                          defer_ok = (uu___158_7746.defer_ok);
                                          smt_ok = (uu___158_7746.smt_ok);
                                          tcenv = (uu___158_7746.tcenv)
                                        }) in
                                   match uu____7745 with
                                   | Success uu____7748 ->
                                       let wl1 =
                                         let uu___159_7750 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7750.wl_deferred);
                                           ctr = (uu___159_7750.ctr);
                                           defer_ok =
                                             (uu___159_7750.defer_ok);
                                           smt_ok = (uu___159_7750.smt_ok);
                                           tcenv = (uu___159_7750.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7752 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7755 -> None))))
                   | uu____7756 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7821 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7821
                      then
                        let uu____7822 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7822
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7854 = hd1 in
                      let uu____7855 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7854.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7854.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7855
                      } in
                    let hd21 =
                      let uu___161_7859 = hd2 in
                      let uu____7860 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7859.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7859.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7860
                      } in
                    let prob =
                      let uu____7864 =
                        let uu____7867 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7867 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7864 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7875 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7875 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7878 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7878 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7896 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7899 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7896 uu____7899 in
                         ((let uu____7905 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7905
                           then
                             let uu____7906 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7907 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7906 uu____7907
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7922 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7928 = aux scope env [] bs1 bs2 in
              match uu____7928 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7944 = compress_tprob wl problem in
        solve_t' env uu____7944 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7977 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7977 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7994,uu____7995) ->
                   let may_relate head3 =
                     let uu____8010 =
                       let uu____8011 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8011.FStar_Syntax_Syntax.n in
                     match uu____8010 with
                     | FStar_Syntax_Syntax.Tm_name uu____8014 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8015 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8032 -> false in
                   let uu____8033 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8033
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
                                let uu____8050 =
                                  let uu____8051 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8051 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8050 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8053 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8053
                   else giveup env1 "head mismatch" orig
               | (uu____8055,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8063 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8063.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8063.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8063.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8063.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8063.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8063.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8063.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8063.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8064,None ) ->
                   ((let uu____8071 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8071
                     then
                       let uu____8072 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8073 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8074 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8075 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8072
                         uu____8073 uu____8074 uu____8075
                     else ());
                    (let uu____8077 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8077 with
                     | (head11,args1) ->
                         let uu____8103 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8103 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8143 =
                                  let uu____8144 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8145 = args_to_string args1 in
                                  let uu____8146 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8147 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8144 uu____8145 uu____8146
                                    uu____8147 in
                                giveup env1 uu____8143 orig
                              else
                                (let uu____8149 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8152 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8152 = FStar_Syntax_Util.Equal) in
                                 if uu____8149
                                 then
                                   let uu____8153 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8153 with
                                   | USolved wl2 ->
                                       let uu____8155 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8155
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8159 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8159 with
                                    | (base1,refinement1) ->
                                        let uu____8185 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8185 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8239 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8239 with
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
                                                           (fun uu____8249 
                                                              ->
                                                              fun uu____8250 
                                                                ->
                                                                match 
                                                                  (uu____8249,
                                                                    uu____8250)
                                                                with
                                                                | ((a,uu____8260),
                                                                   (a',uu____8262))
                                                                    ->
                                                                    let uu____8267
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
                                                                    uu____8267)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8273 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8273 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8277 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_8310 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8310.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8330 = p in
          match uu____8330 with
          | (((u,k),xs,c),ps,(h,uu____8341,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8390 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8390 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8404 = h gs_xs in
                     let uu____8405 =
                       let uu____8412 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8412
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8404 uu____8405 in
                   ((let uu____8443 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8443
                     then
                       let uu____8444 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8445 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8446 = FStar_Syntax_Print.term_to_string im in
                       let uu____8447 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8448 =
                         let uu____8449 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8449
                           (FStar_String.concat ", ") in
                       let uu____8452 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8444 uu____8445 uu____8446 uu____8447
                         uu____8448 uu____8452
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_8470 =
          match uu___129_8470 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8499 = p in
          match uu____8499 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8557 = FStar_List.nth ps i in
              (match uu____8557 with
               | (pi,uu____8560) ->
                   let uu____8565 = FStar_List.nth xs i in
                   (match uu____8565 with
                    | (xi,uu____8572) ->
                        let rec gs k =
                          let uu____8581 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8581 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8633)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8641 = new_uvar r xs k_a in
                                    (match uu____8641 with
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
                                         let uu____8660 = aux subst2 tl1 in
                                         (match uu____8660 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8675 =
                                                let uu____8677 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8677 :: gi_xs' in
                                              let uu____8678 =
                                                let uu____8680 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8680 :: gi_ps' in
                                              (uu____8675, uu____8678))) in
                              aux [] bs in
                        let uu____8683 =
                          let uu____8684 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8684 in
                        if uu____8683
                        then None
                        else
                          (let uu____8687 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8687 with
                           | (g_xs,uu____8694) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8701 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8706 =
                                   let uu____8713 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8713
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8701
                                   uu____8706 in
                               let sub1 =
                                 let uu____8744 =
                                   let uu____8747 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8754 =
                                     let uu____8757 =
                                       FStar_List.map
                                         (fun uu____8763  ->
                                            match uu____8763 with
                                            | (uu____8768,uu____8769,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8757 in
                                   mk_problem (p_scope orig) orig uu____8747
                                     (p_rel orig) uu____8754 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8744 in
                               ((let uu____8779 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8779
                                 then
                                   let uu____8780 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8781 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8780 uu____8781
                                 else ());
                                (let wl2 =
                                   let uu____8784 =
                                     let uu____8786 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8786 in
                                   solve_prob orig uu____8784
                                     [TERM (u, proj)] wl1 in
                                 let uu____8791 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8791))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8815 = lhs in
          match uu____8815 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8838 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8838 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8860 =
                        let uu____8886 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8886) in
                      Some uu____8860
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8969 =
                           let uu____8973 =
                             let uu____8974 = FStar_Syntax_Subst.compress k in
                             uu____8974.FStar_Syntax_Syntax.n in
                           (uu____8973, args) in
                         match uu____8969 with
                         | (uu____8981,[]) ->
                             let uu____8983 =
                               let uu____8989 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8989) in
                             Some uu____8983
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9000,uu____9001) ->
                             let uu____9012 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9012 with
                              | (uv1,uv_args) ->
                                  let uu____9041 =
                                    let uu____9042 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9042.FStar_Syntax_Syntax.n in
                                  (match uu____9041 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9049) ->
                                       let uu____9062 =
                                         pat_vars env [] uv_args in
                                       (match uu____9062 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9076  ->
                                                      let uu____9077 =
                                                        let uu____9078 =
                                                          let uu____9079 =
                                                            let uu____9082 =
                                                              let uu____9083
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9083
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9082 in
                                                          fst uu____9079 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9078 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9077)) in
                                            let c1 =
                                              let uu____9089 =
                                                let uu____9090 =
                                                  let uu____9093 =
                                                    let uu____9094 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9094
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9093 in
                                                fst uu____9090 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9089 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9103 =
                                                let uu____9110 =
                                                  let uu____9116 =
                                                    let uu____9117 =
                                                      let uu____9120 =
                                                        let uu____9121 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9121
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9120 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9117 in
                                                  FStar_Util.Inl uu____9116 in
                                                Some uu____9110 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9103 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____9144 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9147,uu____9148)
                             ->
                             let uu____9160 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9160 with
                              | (uv1,uv_args) ->
                                  let uu____9189 =
                                    let uu____9190 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9190.FStar_Syntax_Syntax.n in
                                  (match uu____9189 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9197) ->
                                       let uu____9210 =
                                         pat_vars env [] uv_args in
                                       (match uu____9210 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9224  ->
                                                      let uu____9225 =
                                                        let uu____9226 =
                                                          let uu____9227 =
                                                            let uu____9230 =
                                                              let uu____9231
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9231
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9230 in
                                                          fst uu____9227 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9226 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9225)) in
                                            let c1 =
                                              let uu____9237 =
                                                let uu____9238 =
                                                  let uu____9241 =
                                                    let uu____9242 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9242
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9241 in
                                                fst uu____9238 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9237 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9251 =
                                                let uu____9258 =
                                                  let uu____9264 =
                                                    let uu____9265 =
                                                      let uu____9268 =
                                                        let uu____9269 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9269
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9268 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9265 in
                                                  FStar_Util.Inl uu____9264 in
                                                Some uu____9258 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9251 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____9292 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9297)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9323 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9323
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9342 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9342 with
                                  | (args1,rest) ->
                                      let uu____9358 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9358 with
                                       | (xs2,c2) ->
                                           let uu____9366 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9366
                                             (fun uu____9377  ->
                                                match uu____9377 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9399 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9399 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9445 =
                                        let uu____9448 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9448 in
                                      FStar_All.pipe_right uu____9445
                                        (fun _0_57  -> Some _0_57))
                         | uu____9456 ->
                             let uu____9460 =
                               let uu____9461 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9465 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9466 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9461 uu____9465 uu____9466 in
                             failwith uu____9460 in
                       let uu____9470 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9470
                         (fun uu____9498  ->
                            match uu____9498 with
                            | (xs1,c1) ->
                                let uu____9526 =
                                  let uu____9549 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9549) in
                                Some uu____9526)) in
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
                     let uu____9621 = imitate orig env wl1 st in
                     match uu____9621 with
                     | Failed uu____9626 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9632 = project orig env wl1 i st in
                      match uu____9632 with
                      | None  ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9639) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9653 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9653 with
                | (hd1,uu____9664) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9679 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9687 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9688 -> true
                     | uu____9703 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9706 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9706
                         then true
                         else
                           ((let uu____9709 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9709
                             then
                               let uu____9710 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9710
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9718 =
                    let uu____9721 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9721 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9718 FStar_Syntax_Free.names in
                let uu____9752 = FStar_Util.set_is_empty fvs_hd in
                if uu____9752
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9761 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9761 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9769 =
                            let uu____9770 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9770 in
                          giveup_or_defer1 orig uu____9769
                        else
                          (let uu____9772 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9772
                           then
                             let uu____9773 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9773
                              then
                                let uu____9774 = subterms args_lhs in
                                imitate' orig env wl1 uu____9774
                              else
                                ((let uu____9778 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9778
                                  then
                                    let uu____9779 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9780 = names_to_string fvs1 in
                                    let uu____9781 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9779 uu____9780 uu____9781
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9786 ->
                                        let uu____9787 = sn_binders env vars in
                                        u_abs k_uv uu____9787 t21 in
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
                               (let uu____9796 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9796
                                then
                                  ((let uu____9798 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9798
                                    then
                                      let uu____9799 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9800 = names_to_string fvs1 in
                                      let uu____9801 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9799 uu____9800 uu____9801
                                    else ());
                                   (let uu____9803 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9803
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
                     (let uu____9814 =
                        let uu____9815 = FStar_Syntax_Free.names t1 in
                        check_head uu____9815 t2 in
                      if uu____9814
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9819 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9819
                          then
                            let uu____9820 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9820
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9823 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9823 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9865 =
               match uu____9865 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____9896 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____9896 with
                    | (all_formals,uu____9907) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9999  ->
                                        match uu____9999 with
                                        | (x,imp) ->
                                            let uu____10006 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10006, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10014 = FStar_Syntax_Util.type_u () in
                                match uu____10014 with
                                | (t1,uu____10018) ->
                                    let uu____10019 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10019 in
                              let uu____10022 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10022 with
                               | (t',tm_u1) ->
                                   let uu____10029 = destruct_flex_t t' in
                                   (match uu____10029 with
                                    | (uu____10049,u1,k11,uu____10052) ->
                                        let sol =
                                          let uu____10080 =
                                            let uu____10085 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10085) in
                                          TERM uu____10080 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10145 = pat_var_opt env pat_args hd1 in
                              (match uu____10145 with
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
                                              (fun uu____10174  ->
                                                 match uu____10174 with
                                                 | (x,uu____10178) ->
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
                                      let uu____10184 =
                                        let uu____10185 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10185 in
                                      if uu____10184
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10189 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10189 formals1
                                           tl1)))
                          | uu____10195 -> failwith "Impossible" in
                        let uu____10206 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10206 all_formals args) in
             let solve_both_pats wl1 uu____10254 uu____10255 r =
               match (uu____10254, uu____10255) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10409 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____10409
                   then
                     let uu____10413 = solve_prob orig None [] wl1 in
                     solve env uu____10413
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10428 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10428
                       then
                         let uu____10429 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10430 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10431 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10432 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10433 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10429 uu____10430 uu____10431 uu____10432
                           uu____10433
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10475 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10475 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10483 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10483 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10513 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10513 in
                                  let uu____10516 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10516 k3)
                           else
                             (let uu____10519 =
                                let uu____10520 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10521 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10522 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10520 uu____10521 uu____10522 in
                              failwith uu____10519) in
                       let uu____10523 =
                         let uu____10529 =
                           let uu____10537 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10537 in
                         match uu____10529 with
                         | (bs,k1') ->
                             let uu____10555 =
                               let uu____10563 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10563 in
                             (match uu____10555 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10584 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10584 in
                                  let uu____10589 =
                                    let uu____10592 =
                                      let uu____10593 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10593.FStar_Syntax_Syntax.n in
                                    let uu____10596 =
                                      let uu____10597 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10597.FStar_Syntax_Syntax.n in
                                    (uu____10592, uu____10596) in
                                  (match uu____10589 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10605,uu____10606) ->
                                       (k1', [sub_prob])
                                   | (uu____10610,FStar_Syntax_Syntax.Tm_type
                                      uu____10611) -> (k2', [sub_prob])
                                   | uu____10615 ->
                                       let uu____10618 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10618 with
                                        | (t,uu____10627) ->
                                            let uu____10628 = new_uvar r zs t in
                                            (match uu____10628 with
                                             | (k_zs,uu____10637) ->
                                                 let kprob =
                                                   let uu____10639 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10639 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10523 with
                       | (k_u',sub_probs) ->
                           let uu____10653 =
                             let uu____10661 =
                               let uu____10662 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10662 in
                             let uu____10667 =
                               let uu____10670 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10670 in
                             let uu____10673 =
                               let uu____10676 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10676 in
                             (uu____10661, uu____10667, uu____10673) in
                           (match uu____10653 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10695 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10695 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10719 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____10719
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10726 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10726 with
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
             let solve_one_pat uu____10778 uu____10779 =
               match (uu____10778, uu____10779) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10883 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10883
                     then
                       let uu____10884 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10885 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10884 uu____10885
                     else ());
                    (let uu____10887 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____10887
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10897  ->
                              fun uu____10898  ->
                                match (uu____10897, uu____10898) with
                                | ((a,uu____10908),(t21,uu____10910)) ->
                                    let uu____10915 =
                                      let uu____10918 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10918
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10915
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10922 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10922 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10932 = occurs_check env wl (u1, k1) t21 in
                        match uu____10932 with
                        | (occurs_ok,uu____10941) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10946 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10946
                            then
                              let sol =
                                let uu____10948 =
                                  let uu____10953 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10953) in
                                TERM uu____10948 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10966 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10966
                               then
                                 let uu____10967 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10967 with
                                 | (sol,(uu____10981,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10991 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10991
                                       then
                                         let uu____10992 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10992
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10997 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10999 = lhs in
             match uu____10999 with
             | (t1,u1,k1,args1) ->
                 let uu____11004 = rhs in
                 (match uu____11004 with
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
                       | uu____11030 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11036 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____11036 with
                              | (sol,uu____11043) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____11046 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____11046
                                    then
                                      let uu____11047 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11047
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11052 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____11054 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____11054
        then
          let uu____11055 = solve_prob orig None [] wl in
          solve env uu____11055
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____11059 = FStar_Util.physical_equality t1 t2 in
           if uu____11059
           then
             let uu____11060 = solve_prob orig None [] wl in
             solve env uu____11060
           else
             ((let uu____11063 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____11063
               then
                 let uu____11064 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____11064
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11067,uu____11068) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11069,FStar_Syntax_Syntax.Tm_bvar uu____11070) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_11110 =
                     match uu___130_11110 with
                     | [] -> c
                     | bs ->
                         let uu____11124 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11124 in
                   let uu____11134 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11134 with
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
                                   let uu____11220 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11220
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11222 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11222))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11299 =
                     match uu___131_11299 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11334 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11334 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11417 =
                                   let uu____11420 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11421 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11420
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11421 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11417))
               | (FStar_Syntax_Syntax.Tm_abs uu____11424,uu____11425) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11448 -> true
                     | uu____11463 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11491 =
                     let uu____11502 = maybe_eta t1 in
                     let uu____11507 = maybe_eta t2 in
                     (uu____11502, uu____11507) in
                   (match uu____11491 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11538 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11538.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11538.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11538.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11538.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11538.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11538.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11538.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11538.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11557 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11557
                        then
                          let uu____11558 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11558 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11579 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11579
                        then
                          let uu____11580 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11580 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11585 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11596,FStar_Syntax_Syntax.Tm_abs uu____11597) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11620 -> true
                     | uu____11635 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11663 =
                     let uu____11674 = maybe_eta t1 in
                     let uu____11679 = maybe_eta t2 in
                     (uu____11674, uu____11679) in
                   (match uu____11663 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11710 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11710.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11710.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11710.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11710.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11710.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11710.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11710.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11710.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11729 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11729
                        then
                          let uu____11730 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11730 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11751 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11751
                        then
                          let uu____11752 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11752 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11757 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11768,FStar_Syntax_Syntax.Tm_refine uu____11769) ->
                   let uu____11778 = as_refinement env wl t1 in
                   (match uu____11778 with
                    | (x1,phi1) ->
                        let uu____11783 = as_refinement env wl t2 in
                        (match uu____11783 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11789 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11789 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11822 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11822
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11826 =
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
                                 let uu____11832 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11832 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11839 =
                                   let uu____11842 =
                                     let uu____11843 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11843 :: (p_scope orig) in
                                   mk_problem uu____11842 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11839 in
                               let uu____11846 =
                                 solve env1
                                   (let uu___165_11847 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_11847.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_11847.smt_ok);
                                      tcenv = (uu___165_11847.tcenv)
                                    }) in
                               (match uu____11846 with
                                | Failed uu____11851 -> fallback ()
                                | Success uu____11854 ->
                                    let guard =
                                      let uu____11858 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11861 =
                                        let uu____11862 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11862
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11858
                                        uu____11861 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___166_11869 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_11869.attempting);
                                        wl_deferred =
                                          (uu___166_11869.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_11869.defer_ok);
                                        smt_ok = (uu___166_11869.smt_ok);
                                        tcenv = (uu___166_11869.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11871,FStar_Syntax_Syntax.Tm_uvar uu____11872) ->
                   let uu____11889 = destruct_flex_t t1 in
                   let uu____11890 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11889 uu____11890
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11891;
                     FStar_Syntax_Syntax.tk = uu____11892;
                     FStar_Syntax_Syntax.pos = uu____11893;
                     FStar_Syntax_Syntax.vars = uu____11894;_},uu____11895),FStar_Syntax_Syntax.Tm_uvar
                  uu____11896) ->
                   let uu____11927 = destruct_flex_t t1 in
                   let uu____11928 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11927 uu____11928
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11929,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11930;
                     FStar_Syntax_Syntax.tk = uu____11931;
                     FStar_Syntax_Syntax.pos = uu____11932;
                     FStar_Syntax_Syntax.vars = uu____11933;_},uu____11934))
                   ->
                   let uu____11965 = destruct_flex_t t1 in
                   let uu____11966 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11965 uu____11966
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11967;
                     FStar_Syntax_Syntax.tk = uu____11968;
                     FStar_Syntax_Syntax.pos = uu____11969;
                     FStar_Syntax_Syntax.vars = uu____11970;_},uu____11971),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11972;
                     FStar_Syntax_Syntax.tk = uu____11973;
                     FStar_Syntax_Syntax.pos = uu____11974;
                     FStar_Syntax_Syntax.vars = uu____11975;_},uu____11976))
                   ->
                   let uu____12021 = destruct_flex_t t1 in
                   let uu____12022 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12021 uu____12022
               | (FStar_Syntax_Syntax.Tm_uvar uu____12023,uu____12024) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12033 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12033 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12037;
                     FStar_Syntax_Syntax.tk = uu____12038;
                     FStar_Syntax_Syntax.pos = uu____12039;
                     FStar_Syntax_Syntax.vars = uu____12040;_},uu____12041),uu____12042)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12065 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12065 t2 wl
               | (uu____12069,FStar_Syntax_Syntax.Tm_uvar uu____12070) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12079,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12080;
                     FStar_Syntax_Syntax.tk = uu____12081;
                     FStar_Syntax_Syntax.pos = uu____12082;
                     FStar_Syntax_Syntax.vars = uu____12083;_},uu____12084))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12107,FStar_Syntax_Syntax.Tm_type uu____12108) ->
                   solve_t' env
                     (let uu___167_12117 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12117.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12117.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12117.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12117.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12117.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12117.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12117.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12117.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12117.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12118;
                     FStar_Syntax_Syntax.tk = uu____12119;
                     FStar_Syntax_Syntax.pos = uu____12120;
                     FStar_Syntax_Syntax.vars = uu____12121;_},uu____12122),FStar_Syntax_Syntax.Tm_type
                  uu____12123) ->
                   solve_t' env
                     (let uu___167_12146 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12146.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12146.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12146.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12146.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12146.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12146.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12146.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12146.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12146.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12147,FStar_Syntax_Syntax.Tm_arrow uu____12148) ->
                   solve_t' env
                     (let uu___167_12164 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12164.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12164.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12164.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12164.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12164.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12164.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12164.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12164.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12164.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12165;
                     FStar_Syntax_Syntax.tk = uu____12166;
                     FStar_Syntax_Syntax.pos = uu____12167;
                     FStar_Syntax_Syntax.vars = uu____12168;_},uu____12169),FStar_Syntax_Syntax.Tm_arrow
                  uu____12170) ->
                   solve_t' env
                     (let uu___167_12200 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12200.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12200.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12200.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12200.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12200.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12200.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12200.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12200.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12200.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12201,uu____12202) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12213 =
                        let uu____12214 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12214 in
                      if uu____12213
                      then
                        let uu____12215 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_12218 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12218.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12218.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12218.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12218.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12218.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12218.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12218.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12218.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12218.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12219 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12215 uu____12219 t2
                          wl
                      else
                        (let uu____12224 = base_and_refinement env wl t2 in
                         match uu____12224 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12254 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_12257 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12257.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12257.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12257.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12257.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12257.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12257.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12257.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12257.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12257.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12258 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12254
                                    uu____12258 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12273 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12273.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12273.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12276 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12276 in
                                  let guard =
                                    let uu____12284 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12284
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12290;
                     FStar_Syntax_Syntax.tk = uu____12291;
                     FStar_Syntax_Syntax.pos = uu____12292;
                     FStar_Syntax_Syntax.vars = uu____12293;_},uu____12294),uu____12295)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12320 =
                        let uu____12321 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12321 in
                      if uu____12320
                      then
                        let uu____12322 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_12325 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12325.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12325.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12325.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12325.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12325.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12325.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12325.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12325.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12325.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12326 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12322 uu____12326 t2
                          wl
                      else
                        (let uu____12331 = base_and_refinement env wl t2 in
                         match uu____12331 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12361 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_12364 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12364.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12364.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12364.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12364.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12364.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12364.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12364.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12364.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12364.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12365 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12361
                                    uu____12365 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12380 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12380.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12380.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12383 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12383 in
                                  let guard =
                                    let uu____12391 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12391
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12397,FStar_Syntax_Syntax.Tm_uvar uu____12398) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12408 = base_and_refinement env wl t1 in
                      match uu____12408 with
                      | (t_base,uu____12419) ->
                          solve_t env
                            (let uu___171_12434 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12434.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12434.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12434.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12434.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12434.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12434.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12434.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12434.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12437,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12438;
                     FStar_Syntax_Syntax.tk = uu____12439;
                     FStar_Syntax_Syntax.pos = uu____12440;
                     FStar_Syntax_Syntax.vars = uu____12441;_},uu____12442))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12466 = base_and_refinement env wl t1 in
                      match uu____12466 with
                      | (t_base,uu____12477) ->
                          solve_t env
                            (let uu___171_12492 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12492.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12492.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12492.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12492.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12492.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12492.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12492.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12492.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12495,uu____12496) ->
                   let t21 =
                     let uu____12504 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12504 in
                   solve_t env
                     (let uu___172_12517 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_12517.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_12517.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_12517.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_12517.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_12517.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_12517.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_12517.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_12517.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_12517.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12518,FStar_Syntax_Syntax.Tm_refine uu____12519) ->
                   let t11 =
                     let uu____12527 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12527 in
                   solve_t env
                     (let uu___173_12540 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12540.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12540.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_12540.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_12540.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12540.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12540.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12540.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12540.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12540.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12543,uu____12544) ->
                   let head1 =
                     let uu____12563 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12563 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12594 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12594 FStar_Pervasives.fst in
                   let uu____12622 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12622
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12631 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12631
                      then
                        let guard =
                          let uu____12638 =
                            let uu____12639 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12639 = FStar_Syntax_Util.Equal in
                          if uu____12638
                          then None
                          else
                            (let uu____12642 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12642) in
                        let uu____12644 = solve_prob orig guard [] wl in
                        solve env uu____12644
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12647,uu____12648) ->
                   let head1 =
                     let uu____12656 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12656 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12687 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12687 FStar_Pervasives.fst in
                   let uu____12715 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12715
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12724 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12724
                      then
                        let guard =
                          let uu____12731 =
                            let uu____12732 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12732 = FStar_Syntax_Util.Equal in
                          if uu____12731
                          then None
                          else
                            (let uu____12735 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12735) in
                        let uu____12737 = solve_prob orig guard [] wl in
                        solve env uu____12737
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12740,uu____12741) ->
                   let head1 =
                     let uu____12745 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12745 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12776 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12776 FStar_Pervasives.fst in
                   let uu____12804 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12804
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12813 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12813
                      then
                        let guard =
                          let uu____12820 =
                            let uu____12821 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12821 = FStar_Syntax_Util.Equal in
                          if uu____12820
                          then None
                          else
                            (let uu____12824 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12824) in
                        let uu____12826 = solve_prob orig guard [] wl in
                        solve env uu____12826
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12829,uu____12830) ->
                   let head1 =
                     let uu____12834 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12834 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12865 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12865 FStar_Pervasives.fst in
                   let uu____12893 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12893
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12902 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12902
                      then
                        let guard =
                          let uu____12909 =
                            let uu____12910 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12910 = FStar_Syntax_Util.Equal in
                          if uu____12909
                          then None
                          else
                            (let uu____12913 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12913) in
                        let uu____12915 = solve_prob orig guard [] wl in
                        solve env uu____12915
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12918,uu____12919) ->
                   let head1 =
                     let uu____12923 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12923 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12954 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12954 FStar_Pervasives.fst in
                   let uu____12982 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12982
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12991 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12991
                      then
                        let guard =
                          let uu____12998 =
                            let uu____12999 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12999 = FStar_Syntax_Util.Equal in
                          if uu____12998
                          then None
                          else
                            (let uu____13002 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____13002) in
                        let uu____13004 = solve_prob orig guard [] wl in
                        solve env uu____13004
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13007,uu____13008) ->
                   let head1 =
                     let uu____13021 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13021 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13052 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13052 FStar_Pervasives.fst in
                   let uu____13080 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13080
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13089 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13089
                      then
                        let guard =
                          let uu____13096 =
                            let uu____13097 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13097 = FStar_Syntax_Util.Equal in
                          if uu____13096
                          then None
                          else
                            (let uu____13100 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____13100) in
                        let uu____13102 = solve_prob orig guard [] wl in
                        solve env uu____13102
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13105,FStar_Syntax_Syntax.Tm_match uu____13106) ->
                   let head1 =
                     let uu____13125 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13125 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13156 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13156 FStar_Pervasives.fst in
                   let uu____13184 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13184
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13193 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13193
                      then
                        let guard =
                          let uu____13200 =
                            let uu____13201 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13201 = FStar_Syntax_Util.Equal in
                          if uu____13200
                          then None
                          else
                            (let uu____13204 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____13204) in
                        let uu____13206 = solve_prob orig guard [] wl in
                        solve env uu____13206
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13209,FStar_Syntax_Syntax.Tm_uinst uu____13210) ->
                   let head1 =
                     let uu____13218 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13218 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13249 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13249 FStar_Pervasives.fst in
                   let uu____13277 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13277
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13286 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13286
                      then
                        let guard =
                          let uu____13293 =
                            let uu____13294 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13294 = FStar_Syntax_Util.Equal in
                          if uu____13293
                          then None
                          else
                            (let uu____13297 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13297) in
                        let uu____13299 = solve_prob orig guard [] wl in
                        solve env uu____13299
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13302,FStar_Syntax_Syntax.Tm_name uu____13303) ->
                   let head1 =
                     let uu____13307 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13307 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13338 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13338 FStar_Pervasives.fst in
                   let uu____13366 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13366
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13375 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13375
                      then
                        let guard =
                          let uu____13382 =
                            let uu____13383 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13383 = FStar_Syntax_Util.Equal in
                          if uu____13382
                          then None
                          else
                            (let uu____13386 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13386) in
                        let uu____13388 = solve_prob orig guard [] wl in
                        solve env uu____13388
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13391,FStar_Syntax_Syntax.Tm_constant uu____13392) ->
                   let head1 =
                     let uu____13396 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13396 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13427 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13427 FStar_Pervasives.fst in
                   let uu____13455 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13455
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13464 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13464
                      then
                        let guard =
                          let uu____13471 =
                            let uu____13472 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13472 = FStar_Syntax_Util.Equal in
                          if uu____13471
                          then None
                          else
                            (let uu____13475 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13475) in
                        let uu____13477 = solve_prob orig guard [] wl in
                        solve env uu____13477
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13480,FStar_Syntax_Syntax.Tm_fvar uu____13481) ->
                   let head1 =
                     let uu____13485 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13485 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13516 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13516 FStar_Pervasives.fst in
                   let uu____13544 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13544
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13553 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13553
                      then
                        let guard =
                          let uu____13560 =
                            let uu____13561 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13561 = FStar_Syntax_Util.Equal in
                          if uu____13560
                          then None
                          else
                            (let uu____13564 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13564) in
                        let uu____13566 = solve_prob orig guard [] wl in
                        solve env uu____13566
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13569,FStar_Syntax_Syntax.Tm_app uu____13570) ->
                   let head1 =
                     let uu____13583 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13583 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13614 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13614 FStar_Pervasives.fst in
                   let uu____13642 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13642
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13651 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13651
                      then
                        let guard =
                          let uu____13658 =
                            let uu____13659 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13659 = FStar_Syntax_Util.Equal in
                          if uu____13658
                          then None
                          else
                            (let uu____13662 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13662) in
                        let uu____13664 = solve_prob orig guard [] wl in
                        solve env uu____13664
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13668,uu____13669),uu____13670) ->
                   solve_t' env
                     (let uu___174_13699 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_13699.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_13699.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_13699.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_13699.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_13699.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_13699.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_13699.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_13699.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_13699.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13702,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13704,uu____13705)) ->
                   solve_t' env
                     (let uu___175_13734 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13734.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_13734.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13734.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_13734.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13734.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13734.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13734.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13734.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13734.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13735,uu____13736) ->
                   let uu____13744 =
                     let uu____13745 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13746 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13745
                       uu____13746 in
                   failwith uu____13744
               | (FStar_Syntax_Syntax.Tm_meta uu____13747,uu____13748) ->
                   let uu____13753 =
                     let uu____13754 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13755 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13754
                       uu____13755 in
                   failwith uu____13753
               | (FStar_Syntax_Syntax.Tm_delayed uu____13756,uu____13757) ->
                   let uu____13778 =
                     let uu____13779 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13780 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13779
                       uu____13780 in
                   failwith uu____13778
               | (uu____13781,FStar_Syntax_Syntax.Tm_meta uu____13782) ->
                   let uu____13787 =
                     let uu____13788 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13789 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13788
                       uu____13789 in
                   failwith uu____13787
               | (uu____13790,FStar_Syntax_Syntax.Tm_delayed uu____13791) ->
                   let uu____13812 =
                     let uu____13813 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13814 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13813
                       uu____13814 in
                   failwith uu____13812
               | (uu____13815,FStar_Syntax_Syntax.Tm_let uu____13816) ->
                   let uu____13824 =
                     let uu____13825 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13826 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13825
                       uu____13826 in
                   failwith uu____13824
               | uu____13827 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13859 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13859
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13867  ->
                  fun uu____13868  ->
                    match (uu____13867, uu____13868) with
                    | ((a1,uu____13878),(a2,uu____13880)) ->
                        let uu____13885 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13885)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13891 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13891 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13911 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13918)::[] -> wp1
              | uu____13931 ->
                  let uu____13937 =
                    let uu____13938 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13938 in
                  failwith uu____13937 in
            let uu____13941 =
              let uu____13947 =
                let uu____13948 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13948 in
              [uu____13947] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13941;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13949 = lift_c1 () in solve_eq uu____13949 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13953  ->
                       match uu___132_13953 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13954 -> false)) in
             let uu____13955 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13979)::uu____13980,(wp2,uu____13982)::uu____13983)
                   -> (wp1, wp2)
               | uu____14024 ->
                   let uu____14037 =
                     let uu____14038 =
                       let uu____14041 =
                         let uu____14042 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____14043 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14042 uu____14043 in
                       (uu____14041, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____14038 in
                   raise uu____14037 in
             match uu____13955 with
             | (wpc1,wpc2) ->
                 let uu____14060 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____14060
                 then
                   let uu____14063 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____14063 wl
                 else
                   (let uu____14067 =
                      let uu____14071 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14071 in
                    match uu____14067 with
                    | (c2_decl,qualifiers) ->
                        let uu____14083 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14083
                        then
                          let c1_repr =
                            let uu____14086 =
                              let uu____14087 =
                                let uu____14088 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14088 in
                              let uu____14089 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14087 uu____14089 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14086 in
                          let c2_repr =
                            let uu____14091 =
                              let uu____14092 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14093 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14092 uu____14093 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14091 in
                          let prob =
                            let uu____14095 =
                              let uu____14098 =
                                let uu____14099 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14100 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14099
                                  uu____14100 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14098 in
                            FStar_TypeChecker_Common.TProb uu____14095 in
                          let wl1 =
                            let uu____14102 =
                              let uu____14104 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14104 in
                            solve_prob orig uu____14102 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14111 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14111
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14113 =
                                     let uu____14116 =
                                       let uu____14117 =
                                         let uu____14127 =
                                           let uu____14128 =
                                             let uu____14129 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14129] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14128 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14130 =
                                           let uu____14132 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14133 =
                                             let uu____14135 =
                                               let uu____14136 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14136 in
                                             [uu____14135] in
                                           uu____14132 :: uu____14133 in
                                         (uu____14127, uu____14130) in
                                       FStar_Syntax_Syntax.Tm_app uu____14117 in
                                     FStar_Syntax_Syntax.mk uu____14116 in
                                   uu____14113
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14147 =
                                    let uu____14150 =
                                      let uu____14151 =
                                        let uu____14161 =
                                          let uu____14162 =
                                            let uu____14163 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14163] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14162 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14164 =
                                          let uu____14166 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14167 =
                                            let uu____14169 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14170 =
                                              let uu____14172 =
                                                let uu____14173 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14173 in
                                              [uu____14172] in
                                            uu____14169 :: uu____14170 in
                                          uu____14166 :: uu____14167 in
                                        (uu____14161, uu____14164) in
                                      FStar_Syntax_Syntax.Tm_app uu____14151 in
                                    FStar_Syntax_Syntax.mk uu____14150 in
                                  uu____14147
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14184 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14184 in
                           let wl1 =
                             let uu____14190 =
                               let uu____14192 =
                                 let uu____14195 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14195 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____14192 in
                             solve_prob orig uu____14190 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14205 = FStar_Util.physical_equality c1 c2 in
        if uu____14205
        then
          let uu____14206 = solve_prob orig None [] wl in
          solve env uu____14206
        else
          ((let uu____14209 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14209
            then
              let uu____14210 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14211 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14210
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14211
            else ());
           (let uu____14213 =
              let uu____14216 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14217 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14216, uu____14217) in
            match uu____14213 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14221),FStar_Syntax_Syntax.Total
                    (t2,uu____14223)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14236 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14236 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14239,FStar_Syntax_Syntax.Total uu____14240) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14252),FStar_Syntax_Syntax.Total
                    (t2,uu____14254)) ->
                     let uu____14267 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14267 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14271),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14273)) ->
                     let uu____14286 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14286 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14290),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14292)) ->
                     let uu____14305 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14305 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14308,FStar_Syntax_Syntax.Comp uu____14309) ->
                     let uu____14315 =
                       let uu___176_14318 = problem in
                       let uu____14321 =
                         let uu____14322 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14322 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14318.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14321;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14318.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14318.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14318.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14318.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14318.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14318.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14318.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14318.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14315 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14323,FStar_Syntax_Syntax.Comp uu____14324) ->
                     let uu____14330 =
                       let uu___176_14333 = problem in
                       let uu____14336 =
                         let uu____14337 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14337 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14333.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14336;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14333.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14333.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14333.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14333.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14333.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14333.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14333.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14333.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14330 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14338,FStar_Syntax_Syntax.GTotal uu____14339) ->
                     let uu____14345 =
                       let uu___177_14348 = problem in
                       let uu____14351 =
                         let uu____14352 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14352 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14348.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14348.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14348.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14351;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14348.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14348.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14348.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14348.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14348.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14348.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14345 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14353,FStar_Syntax_Syntax.Total uu____14354) ->
                     let uu____14360 =
                       let uu___177_14363 = problem in
                       let uu____14366 =
                         let uu____14367 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14367 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14363.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14363.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14363.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14366;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14363.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14363.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14363.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14363.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14363.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14363.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14360 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14368,FStar_Syntax_Syntax.Comp uu____14369) ->
                     let uu____14370 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14370
                     then
                       let uu____14371 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14371 wl
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
                           (let uu____14381 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14381
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14383 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14383 with
                            | None  ->
                                let uu____14385 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14386 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14386) in
                                if uu____14385
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
                                  (let uu____14389 =
                                     let uu____14390 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14391 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14390 uu____14391 in
                                   giveup env uu____14389 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14396 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14416  ->
              match uu____14416 with
              | (uu____14427,uu____14428,u,uu____14430,uu____14431,uu____14432)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14396 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14461 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14461 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14471 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14483  ->
                match uu____14483 with
                | (u1,u2) ->
                    let uu____14488 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14489 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14488 uu____14489)) in
      FStar_All.pipe_right uu____14471 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14501,[])) -> "{}"
      | uu____14514 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14524 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14524
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14527 =
              FStar_List.map
                (fun uu____14531  ->
                   match uu____14531 with
                   | (uu____14534,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14527 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14538 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14538 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14576 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14576
    then
      let uu____14577 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14578 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14577
        (rel_to_string rel) uu____14578
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
            let uu____14598 =
              let uu____14600 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14600 in
            FStar_Syntax_Syntax.new_bv uu____14598 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14606 =
              let uu____14608 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14608 in
            let uu____14610 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14606 uu____14610 in
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
          let uu____14633 = FStar_Options.eager_inference () in
          if uu____14633
          then
            let uu___178_14634 = probs in
            {
              attempting = (uu___178_14634.attempting);
              wl_deferred = (uu___178_14634.wl_deferred);
              ctr = (uu___178_14634.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14634.smt_ok);
              tcenv = (uu___178_14634.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____14645 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14645
              then
                let uu____14646 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14646
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
          ((let uu____14656 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14656
            then
              let uu____14657 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14657
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14661 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14661
             then
               let uu____14662 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14662
             else ());
            (let f2 =
               let uu____14665 =
                 let uu____14666 = FStar_Syntax_Util.unmeta f1 in
                 uu____14666.FStar_Syntax_Syntax.n in
               match uu____14665 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14670 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_14671 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14671.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14671.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14671.FStar_TypeChecker_Env.implicits)
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
            let uu____14686 =
              let uu____14687 =
                let uu____14688 =
                  let uu____14689 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14689
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14688;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14687 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14686
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14722 =
        let uu____14723 =
          let uu____14724 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14724
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14723;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14722
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
          (let uu____14750 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14750
           then
             let uu____14751 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14752 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14751
               uu____14752
           else ());
          (let prob =
             let uu____14755 =
               let uu____14758 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14758 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14755 in
           let g =
             let uu____14763 =
               let uu____14765 = singleton' env prob smt_ok in
               solve_and_commit env uu____14765 (fun uu____14766  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14763 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14780 = try_teq true env t1 t2 in
        match uu____14780 with
        | None  ->
            let uu____14782 =
              let uu____14783 =
                let uu____14786 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14787 = FStar_TypeChecker_Env.get_range env in
                (uu____14786, uu____14787) in
              FStar_Errors.Error uu____14783 in
            raise uu____14782
        | Some g ->
            ((let uu____14790 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14790
              then
                let uu____14791 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14792 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14793 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14791
                  uu____14792 uu____14793
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
          (let uu____14809 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14809
           then
             let uu____14810 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14811 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14810
               uu____14811
           else ());
          (let uu____14813 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14813 with
           | (prob,x) ->
               let g =
                 let uu____14821 =
                   let uu____14823 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14823
                     (fun uu____14824  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14821 in
               ((let uu____14830 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14830
                 then
                   let uu____14831 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14832 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14833 =
                     let uu____14834 = FStar_Util.must g in
                     guard_to_string env uu____14834 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14831 uu____14832 uu____14833
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
          let uu____14858 = FStar_TypeChecker_Env.get_range env in
          let uu____14859 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14858 uu____14859
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14871 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14871
         then
           let uu____14872 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14873 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14872
             uu____14873
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14878 =
             let uu____14881 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14881 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14878 in
         let uu____14884 =
           let uu____14886 = singleton env prob in
           solve_and_commit env uu____14886 (fun uu____14887  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14884)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14906  ->
        match uu____14906 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____14931 =
                 let uu____14932 =
                   let uu____14935 =
                     let uu____14936 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14937 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14936 uu____14937 in
                   let uu____14938 = FStar_TypeChecker_Env.get_range env in
                   (uu____14935, uu____14938) in
                 FStar_Errors.Error uu____14932 in
               raise uu____14931) in
            let equiv v1 v' =
              let uu____14946 =
                let uu____14949 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14950 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14949, uu____14950) in
              match uu____14946 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____14958 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14972 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14972 with
                      | FStar_Syntax_Syntax.U_unif uu____14976 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14987  ->
                                    match uu____14987 with
                                    | (u,v') ->
                                        let uu____14993 = equiv v1 v' in
                                        if uu____14993
                                        then
                                          let uu____14995 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____14995 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____15005 -> [])) in
            let uu____15008 =
              let wl =
                let uu___180_15011 = empty_worklist env in
                {
                  attempting = (uu___180_15011.attempting);
                  wl_deferred = (uu___180_15011.wl_deferred);
                  ctr = (uu___180_15011.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_15011.smt_ok);
                  tcenv = (uu___180_15011.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15018  ->
                      match uu____15018 with
                      | (lb,v1) ->
                          let uu____15023 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____15023 with
                           | USolved wl1 -> ()
                           | uu____15025 -> fail lb v1))) in
            let rec check_ineq uu____15031 =
              match uu____15031 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15038) -> true
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
                      uu____15050,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15052,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15057) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15061,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15066 -> false) in
            let uu____15069 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15075  ->
                      match uu____15075 with
                      | (u,v1) ->
                          let uu____15080 = check_ineq (u, v1) in
                          if uu____15080
                          then true
                          else
                            ((let uu____15083 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15083
                              then
                                let uu____15084 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15085 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15084
                                  uu____15085
                              else ());
                             false))) in
            if uu____15069
            then ()
            else
              ((let uu____15089 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15089
                then
                  ((let uu____15091 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15091);
                   FStar_Unionfind.rollback tx;
                   (let uu____15097 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15097))
                else ());
               (let uu____15103 =
                  let uu____15104 =
                    let uu____15107 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15107) in
                  FStar_Errors.Error uu____15104 in
                raise uu____15103))
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
      let fail uu____15140 =
        match uu____15140 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15150 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15150
       then
         let uu____15151 = wl_to_string wl in
         let uu____15152 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15151 uu____15152
       else ());
      (let g1 =
         let uu____15164 = solve_and_commit env wl fail in
         match uu____15164 with
         | Some [] ->
             let uu___181_15171 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15171.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15171.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15171.FStar_TypeChecker_Env.implicits)
             }
         | uu____15174 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15177 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15177.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15177.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15177.FStar_TypeChecker_Env.implicits)
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
            let uu___183_15203 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15203.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15203.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15203.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15204 =
            let uu____15205 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15205 in
          if uu____15204
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15211 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15211
                   then
                     let uu____15212 = FStar_TypeChecker_Env.get_range env in
                     let uu____15213 =
                       let uu____15214 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15214 in
                     FStar_Errors.diag uu____15212 uu____15213
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
                         ((let uu____15223 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15223
                           then
                             let uu____15224 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15225 =
                               let uu____15226 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15226 in
                             FStar_Errors.diag uu____15224 uu____15225
                           else ());
                          (let vcs =
                             let uu____15232 = FStar_Options.use_tactics () in
                             if uu____15232
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15246  ->
                                   match uu____15246 with
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
      let uu____15257 = discharge_guard' None env g false in
      match uu____15257 with
      | Some g1 -> g1
      | None  ->
          let uu____15262 =
            let uu____15263 =
              let uu____15266 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15266) in
            FStar_Errors.Error uu____15263 in
          raise uu____15262
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15273 = discharge_guard' None env g true in
      match uu____15273 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15293 = FStar_Unionfind.find u in
      match uu____15293 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____15302 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15317 = acc in
      match uu____15317 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15363 = hd1 in
               (match uu____15363 with
                | (uu____15370,env,u,tm,k,r) ->
                    let uu____15376 = unresolved u in
                    if uu____15376
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15394 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15394
                        then
                          let uu____15395 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15399 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15400 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15395 uu____15399 uu____15400
                        else ());
                       (let uu____15402 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15406 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15406.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15406.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15406.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15406.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15406.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15406.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15406.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15406.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15406.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15406.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15406.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15406.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15406.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15406.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15406.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15406.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15406.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15406.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15406.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15406.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15406.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15406.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15406.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____15402 with
                        | (uu____15407,uu____15408,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15411 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15411.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15411.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15411.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15414 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15418  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15414 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_15433 = g in
    let uu____15434 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15433.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15433.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15433.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15434
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15462 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15462 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15469 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15469
      | (reason,uu____15471,uu____15472,e,t,r)::uu____15476 ->
          let uu____15490 =
            let uu____15491 = FStar_Syntax_Print.term_to_string t in
            let uu____15492 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15491 uu____15492 in
          FStar_Errors.err r uu____15490
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15499 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15499.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15499.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15499.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15517 = try_teq false env t1 t2 in
        match uu____15517 with
        | None  -> false
        | Some g ->
            let uu____15520 = discharge_guard' None env g false in
            (match uu____15520 with
             | Some uu____15524 -> true
             | None  -> false)