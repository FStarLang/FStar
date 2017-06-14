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
  fun uu___105_576  ->
    match uu___105_576 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____589 =
    let uu____590 = FStar_Syntax_Subst.compress t in
    uu____590.FStar_Syntax_Syntax.n in
  match uu____589 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____611 = FStar_Syntax_Print.uvar_to_string u in
      let uu____612 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____611 uu____612
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____615;
         FStar_Syntax_Syntax.pos = uu____616;
         FStar_Syntax_Syntax.vars = uu____617;_},args)
      ->
      let uu____649 = FStar_Syntax_Print.uvar_to_string u in
      let uu____650 = FStar_Syntax_Print.term_to_string ty in
      let uu____651 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____649 uu____650 uu____651
  | uu____652 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_658  ->
      match uu___106_658 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____662 =
            let uu____664 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____665 =
              let uu____667 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____668 =
                let uu____670 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____671 =
                  let uu____673 =
                    let uu____675 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____676 =
                      let uu____678 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____679 =
                        let uu____681 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____682 =
                          let uu____684 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____684] in
                        uu____681 :: uu____682 in
                      uu____678 :: uu____679 in
                    uu____675 :: uu____676 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____673 in
                uu____670 :: uu____671 in
              uu____667 :: uu____668 in
            uu____664 :: uu____665 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____662
      | FStar_TypeChecker_Common.CProb p ->
          let uu____689 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____690 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____689
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____690
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_696  ->
      match uu___107_696 with
      | UNIV (u,t) ->
          let x =
            let uu____700 = FStar_Options.hide_uvar_nums () in
            if uu____700
            then "?"
            else
              (let uu____702 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____702 FStar_Util.string_of_int) in
          let uu____703 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____703
      | TERM ((u,uu____705),t) ->
          let x =
            let uu____710 = FStar_Options.hide_uvar_nums () in
            if uu____710
            then "?"
            else
              (let uu____712 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____712 FStar_Util.string_of_int) in
          let uu____713 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____713
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____722 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____722 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____730 =
      let uu____732 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____732
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____730 (FStar_String.concat ", ")
let args_to_string args =
  let uu____750 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____758  ->
            match uu____758 with
            | (x,uu____762) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____750 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____767 =
      let uu____768 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____768 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____767;
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
        let uu___138_781 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___138_781.wl_deferred);
          ctr = (uu___138_781.ctr);
          defer_ok = (uu___138_781.defer_ok);
          smt_ok;
          tcenv = (uu___138_781.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___139_806 = empty_worklist env in
  let uu____807 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____807;
    wl_deferred = (uu___139_806.wl_deferred);
    ctr = (uu___139_806.ctr);
    defer_ok = false;
    smt_ok = (uu___139_806.smt_ok);
    tcenv = (uu___139_806.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_819 = wl in
        {
          attempting = (uu___140_819.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_819.ctr);
          defer_ok = (uu___140_819.defer_ok);
          smt_ok = (uu___140_819.smt_ok);
          tcenv = (uu___140_819.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___141_831 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_831.wl_deferred);
        ctr = (uu___141_831.ctr);
        defer_ok = (uu___141_831.defer_ok);
        smt_ok = (uu___141_831.smt_ok);
        tcenv = (uu___141_831.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____842 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____842
         then
           let uu____843 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____843
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_847  ->
    match uu___108_847 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___142_863 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_863.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_863.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_863.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_863.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_863.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_863.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_863.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_884  ->
    match uu___109_884 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_900  ->
      match uu___110_900 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_903  ->
    match uu___111_903 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_912  ->
    match uu___112_912 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_922  ->
    match uu___113_922 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_932  ->
    match uu___114_932 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___115_943  ->
    match uu___115_943 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_954  ->
    match uu___116_954 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_963  ->
    match uu___117_963 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____977 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____977 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____988  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1038 = next_pid () in
  let uu____1039 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1038;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1039;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1086 = next_pid () in
  let uu____1087 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1086;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1087;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1128 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1128;
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
        let uu____1180 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1180
        then
          let uu____1181 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1182 = prob_to_string env d in
          let uu____1183 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1181 uu____1182 uu____1183 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1188 -> failwith "impossible" in
           let uu____1189 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1197 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1198 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1197, uu____1198)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1202 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1203 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1202, uu____1203) in
           match uu____1189 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1212  ->
            match uu___118_1212 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1220 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1222),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1235  ->
           match uu___119_1235 with
           | UNIV uu____1237 -> None
           | TERM ((u,uu____1241),t) ->
               let uu____1245 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1245 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1257  ->
           match uu___120_1257 with
           | UNIV (u',t) ->
               let uu____1261 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1261 then Some t else None
           | uu____1264 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1271 =
        let uu____1272 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1272 in
      FStar_Syntax_Subst.compress uu____1271
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1279 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1279
let norm_arg env t = let uu____1298 = sn env (fst t) in (uu____1298, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1315  ->
              match uu____1315 with
              | (x,imp) ->
                  let uu____1322 =
                    let uu___143_1323 = x in
                    let uu____1324 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1323.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1323.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1324
                    } in
                  (uu____1322, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1339 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1339
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1342 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1342
        | uu____1344 -> u2 in
      let uu____1345 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1345
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1452 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1452 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1464;
               FStar_Syntax_Syntax.pos = uu____1465;
               FStar_Syntax_Syntax.vars = uu____1466;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1487 =
                 let uu____1488 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1489 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1488
                   uu____1489 in
               failwith uu____1487)
    | FStar_Syntax_Syntax.Tm_uinst uu____1499 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1526 =
             let uu____1527 = FStar_Syntax_Subst.compress t1' in
             uu____1527.FStar_Syntax_Syntax.n in
           match uu____1526 with
           | FStar_Syntax_Syntax.Tm_refine uu____1539 -> aux true t1'
           | uu____1544 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1556 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1579 =
             let uu____1580 = FStar_Syntax_Subst.compress t1' in
             uu____1580.FStar_Syntax_Syntax.n in
           match uu____1579 with
           | FStar_Syntax_Syntax.Tm_refine uu____1592 -> aux true t1'
           | uu____1597 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1609 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1641 =
             let uu____1642 = FStar_Syntax_Subst.compress t1' in
             uu____1642.FStar_Syntax_Syntax.n in
           match uu____1641 with
           | FStar_Syntax_Syntax.Tm_refine uu____1654 -> aux true t1'
           | uu____1659 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1671 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1683 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1695 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1707 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1719 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1738 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1764 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1786 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1805 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1831 ->
        let uu____1836 =
          let uu____1837 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1838 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1837
            uu____1838 in
        failwith uu____1836
    | FStar_Syntax_Syntax.Tm_ascribed uu____1848 ->
        let uu____1866 =
          let uu____1867 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1868 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1867
            uu____1868 in
        failwith uu____1866
    | FStar_Syntax_Syntax.Tm_delayed uu____1878 ->
        let uu____1899 =
          let uu____1900 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1901 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1900
            uu____1901 in
        failwith uu____1899
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1911 =
          let uu____1912 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1913 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1912
            uu____1913 in
        failwith uu____1911 in
  let uu____1923 = whnf env t1 in aux false uu____1923
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1932 =
        let uu____1942 = empty_worklist env in
        base_and_refinement env uu____1942 t in
      FStar_All.pipe_right uu____1932 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1966 = FStar_Syntax_Syntax.null_bv t in
    (uu____1966, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1986 = base_and_refinement env wl t in
  match uu____1986 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2045 =
  match uu____2045 with
  | (t_base,refopt) ->
      let uu____2059 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2059 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2083  ->
      match uu___121_2083 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2087 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2088 =
            let uu____2089 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2089 in
          let uu____2090 =
            let uu____2091 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2091 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2087 uu____2088
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2090
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2095 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2096 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2097 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2095 uu____2096
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2097
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2101 =
      let uu____2103 =
        let uu____2105 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2115  ->
                  match uu____2115 with | (uu____2119,uu____2120,x) -> x)) in
        FStar_List.append wl.attempting uu____2105 in
      FStar_List.map (wl_prob_to_string wl) uu____2103 in
    FStar_All.pipe_right uu____2101 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2138 =
          let uu____2148 =
            let uu____2149 = FStar_Syntax_Subst.compress k in
            uu____2149.FStar_Syntax_Syntax.n in
          match uu____2148 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2190 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2190)
              else
                (let uu____2204 = FStar_Syntax_Util.abs_formals t in
                 match uu____2204 with
                 | (ys',t1,uu____2225) ->
                     let uu____2238 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2238))
          | uu____2259 ->
              let uu____2260 =
                let uu____2266 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2266) in
              ((ys, t), uu____2260) in
        match uu____2138 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2321 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2321 c in
               let uu____2323 =
                 let uu____2330 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2330 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2323)
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
            let uu____2381 = p_guard prob in
            match uu____2381 with
            | (uu____2384,uv) ->
                ((let uu____2387 =
                    let uu____2388 = FStar_Syntax_Subst.compress uv in
                    uu____2388.FStar_Syntax_Syntax.n in
                  match uu____2387 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2412 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2412
                        then
                          let uu____2413 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2414 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2415 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2413
                            uu____2414 uu____2415
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2417 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2420 = wl in
                  {
                    attempting = (uu___144_2420.attempting);
                    wl_deferred = (uu___144_2420.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2420.defer_ok);
                    smt_ok = (uu___144_2420.smt_ok);
                    tcenv = (uu___144_2420.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2433 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2433
         then
           let uu____2434 = FStar_Util.string_of_int pid in
           let uu____2435 =
             let uu____2436 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2436 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2434 uu____2435
         else ());
        commit sol;
        (let uu___145_2441 = wl in
         {
           attempting = (uu___145_2441.attempting);
           wl_deferred = (uu___145_2441.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2441.defer_ok);
           smt_ok = (uu___145_2441.smt_ok);
           tcenv = (uu___145_2441.tcenv)
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
            | (uu____2470,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2478 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2478 in
          (let uu____2484 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2484
           then
             let uu____2485 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2486 =
               let uu____2487 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2487 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2485 uu____2486
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2512 =
    let uu____2516 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2516 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2512
    (FStar_Util.for_some
       (fun uu____2533  ->
          match uu____2533 with
          | (uv,uu____2537) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2570 = occurs wl uk t in Prims.op_Negation uu____2570 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2575 =
         let uu____2576 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2577 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2576 uu____2577 in
       Some uu____2575) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2625 = occurs_check env wl uk t in
  match uu____2625 with
  | (occurs_ok,msg) ->
      let uu____2642 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2642, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2706 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2730  ->
            fun uu____2731  ->
              match (uu____2730, uu____2731) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2774 =
                    let uu____2775 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2775 in
                  if uu____2774
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2789 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2789
                     then
                       let uu____2796 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2796)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2706 with | (isect,uu____2818) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2867  ->
          fun uu____2868  ->
            match (uu____2867, uu____2868) with
            | ((a,uu____2878),(b,uu____2880)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2924 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2930  ->
                match uu____2930 with
                | (b,uu____2934) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2924 then None else Some (a, (snd hd1))
  | uu____2943 -> None
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
            let uu____2986 = pat_var_opt env seen hd1 in
            (match uu____2986 with
             | None  ->
                 ((let uu____2994 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2994
                   then
                     let uu____2995 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2995
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3007 =
      let uu____3008 = FStar_Syntax_Subst.compress t in
      uu____3008.FStar_Syntax_Syntax.n in
    match uu____3007 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3011 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3022;
           FStar_Syntax_Syntax.tk = uu____3023;
           FStar_Syntax_Syntax.pos = uu____3024;
           FStar_Syntax_Syntax.vars = uu____3025;_},uu____3026)
        -> true
    | uu____3051 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3121;
         FStar_Syntax_Syntax.pos = uu____3122;
         FStar_Syntax_Syntax.vars = uu____3123;_},args)
      -> (t, uv, k, args)
  | uu____3170 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3228 = destruct_flex_t t in
  match uu____3228 with
  | (t1,uv,k,args) ->
      let uu____3304 = pat_vars env [] args in
      (match uu____3304 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3366 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3419 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3442 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3446 -> false
let head_match: match_result -> match_result =
  fun uu___122_3449  ->
    match uu___122_3449 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3458 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3467 ->
          let uu____3468 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3468 with
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
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3553) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3559,uu____3560) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3590) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3605;
             FStar_Syntax_Syntax.index = uu____3606;
             FStar_Syntax_Syntax.sort = t2;_},uu____3608)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3615 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3616 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3617 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3625 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3641 = fv_delta_depth env fv in Some uu____3641
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
            let uu____3660 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3660
            then FullMatch
            else
              (let uu____3662 =
                 let uu____3667 =
                   let uu____3669 = fv_delta_depth env f in Some uu____3669 in
                 let uu____3670 =
                   let uu____3672 = fv_delta_depth env g in Some uu____3672 in
                 (uu____3667, uu____3670) in
               MisMatch uu____3662)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3676),FStar_Syntax_Syntax.Tm_uinst (g,uu____3678)) ->
            let uu____3687 = head_matches env f g in
            FStar_All.pipe_right uu____3687 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3694),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3696)) ->
            let uu____3729 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3729 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3734),FStar_Syntax_Syntax.Tm_refine (y,uu____3736)) ->
            let uu____3745 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3745 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3747),uu____3748) ->
            let uu____3753 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3753 head_match
        | (uu____3754,FStar_Syntax_Syntax.Tm_refine (x,uu____3756)) ->
            let uu____3761 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3761 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3762,FStar_Syntax_Syntax.Tm_type
           uu____3763) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3764,FStar_Syntax_Syntax.Tm_arrow uu____3765) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3781),FStar_Syntax_Syntax.Tm_app (head',uu____3783))
            ->
            let uu____3812 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3812 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3814),uu____3815) ->
            let uu____3830 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3830 head_match
        | (uu____3831,FStar_Syntax_Syntax.Tm_app (head1,uu____3833)) ->
            let uu____3848 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3848 head_match
        | uu____3849 ->
            let uu____3852 =
              let uu____3857 = delta_depth_of_term env t11 in
              let uu____3859 = delta_depth_of_term env t21 in
              (uu____3857, uu____3859) in
            MisMatch uu____3852
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3895 = FStar_Syntax_Util.head_and_args t in
    match uu____3895 with
    | (head1,uu____3907) ->
        let uu____3922 =
          let uu____3923 = FStar_Syntax_Util.un_uinst head1 in
          uu____3923.FStar_Syntax_Syntax.n in
        (match uu____3922 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3928 =
               let uu____3929 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3929 FStar_Option.isSome in
             if uu____3928
             then
               let uu____3939 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3939 (fun _0_38  -> Some _0_38)
             else None
         | uu____3942 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4010) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4020 =
             let uu____4025 = maybe_inline t11 in
             let uu____4027 = maybe_inline t21 in (uu____4025, uu____4027) in
           match uu____4020 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4048,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4058 =
             let uu____4063 = maybe_inline t11 in
             let uu____4065 = maybe_inline t21 in (uu____4063, uu____4065) in
           match uu____4058 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4090 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4090 with
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
        let uu____4105 =
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
             let uu____4113 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4113)) in
        (match uu____4105 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4121 -> fail r
    | uu____4126 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4155 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4185 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4200 = FStar_Syntax_Util.type_u () in
      match uu____4200 with
      | (t,uu____4204) ->
          let uu____4205 = new_uvar r binders t in fst uu____4205
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4214 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4214 FStar_Pervasives.fst
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
        let uu____4256 = head_matches env t1 t' in
        match uu____4256 with
        | MisMatch uu____4257 -> false
        | uu____4262 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4322,imp),T (t2,uu____4325)) -> (t2, imp)
                     | uu____4342 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4382  ->
                    match uu____4382 with
                    | (t2,uu____4390) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4420 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4420 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4473))::tcs2) ->
                       aux
                         (((let uu___146_4495 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4495.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4495.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4505 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_4536 =
                 match uu___123_4536 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4599 = decompose1 [] bs1 in
               (rebuild, matches, uu____4599))
      | uu____4627 ->
          let rebuild uu___124_4632 =
            match uu___124_4632 with
            | [] -> t1
            | uu____4634 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4653  ->
    match uu___125_4653 with
    | T (t,uu____4655) -> t
    | uu____4664 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4667  ->
    match uu___126_4667 with
    | T (t,uu____4669) -> FStar_Syntax_Syntax.as_arg t
    | uu____4678 -> failwith "Impossible"
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
              | (uu____4747,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4766 = new_uvar r scope1 k in
                  (match uu____4766 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4778 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4793 =
                         let uu____4794 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4794 in
                       ((T (gi_xs, mk_kind)), uu____4793))
              | (uu____4803,uu____4804,C uu____4805) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4892 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4903;
                         FStar_Syntax_Syntax.pos = uu____4904;
                         FStar_Syntax_Syntax.vars = uu____4905;_})
                        ->
                        let uu____4920 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4920 with
                         | (T (gi_xs,uu____4936),prob) ->
                             let uu____4946 =
                               let uu____4947 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4947 in
                             (uu____4946, [prob])
                         | uu____4949 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4959;
                         FStar_Syntax_Syntax.pos = uu____4960;
                         FStar_Syntax_Syntax.vars = uu____4961;_})
                        ->
                        let uu____4976 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4976 with
                         | (T (gi_xs,uu____4992),prob) ->
                             let uu____5002 =
                               let uu____5003 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5003 in
                             (uu____5002, [prob])
                         | uu____5005 -> failwith "impossible")
                    | (uu____5011,uu____5012,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5014;
                         FStar_Syntax_Syntax.pos = uu____5015;
                         FStar_Syntax_Syntax.vars = uu____5016;_})
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
                        let uu____5090 =
                          let uu____5095 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5095 FStar_List.unzip in
                        (match uu____5090 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5124 =
                                 let uu____5125 =
                                   let uu____5128 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5128 un_T in
                                 let uu____5129 =
                                   let uu____5135 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5135
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5125;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5129;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5124 in
                             ((C gi_xs), sub_probs))
                    | uu____5140 ->
                        let uu____5147 = sub_prob scope1 args q in
                        (match uu____5147 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4892 with
                   | (tc,probs) ->
                       let uu____5165 =
                         match q with
                         | (Some b,uu____5191,uu____5192) ->
                             let uu____5200 =
                               let uu____5204 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5204 :: args in
                             ((Some b), (b :: scope1), uu____5200)
                         | uu____5222 -> (None, scope1, args) in
                       (match uu____5165 with
                        | (bopt,scope2,args1) ->
                            let uu____5265 = aux scope2 args1 qs2 in
                            (match uu____5265 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5286 =
                                         let uu____5288 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5288 in
                                       FStar_Syntax_Util.mk_conj_l uu____5286
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5301 =
                                         let uu____5303 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5304 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5303 :: uu____5304 in
                                       FStar_Syntax_Util.mk_conj_l uu____5301 in
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
  let uu___147_5357 = p in
  let uu____5360 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5361 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5357.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5360;
    FStar_TypeChecker_Common.relation =
      (uu___147_5357.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5361;
    FStar_TypeChecker_Common.element =
      (uu___147_5357.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5357.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5357.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5357.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5357.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5357.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5371 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5371
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5376 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5390 = compress_prob wl pr in
        FStar_All.pipe_right uu____5390 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5396 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5396 with
           | (lh,uu____5409) ->
               let uu____5424 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5424 with
                | (rh,uu____5437) ->
                    let uu____5452 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5461,FStar_Syntax_Syntax.Tm_uvar uu____5462)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5485,uu____5486)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5499,FStar_Syntax_Syntax.Tm_uvar uu____5500)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5513,uu____5514)
                          ->
                          let uu____5525 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5525 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5565 ->
                                    let rank =
                                      let uu____5572 = is_top_level_prob prob in
                                      if uu____5572
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5574 =
                                      let uu___148_5577 = tp in
                                      let uu____5580 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5577.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5577.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5577.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5580;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5577.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5577.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5577.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5577.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5577.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5577.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5574)))
                      | (uu____5590,FStar_Syntax_Syntax.Tm_uvar uu____5591)
                          ->
                          let uu____5602 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5602 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5642 ->
                                    let uu____5648 =
                                      let uu___149_5653 = tp in
                                      let uu____5656 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5653.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5656;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5653.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5653.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5653.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5653.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5653.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5653.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5653.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5653.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5648)))
                      | (uu____5672,uu____5673) -> (rigid_rigid, tp) in
                    (match uu____5452 with
                     | (rank,tp1) ->
                         let uu____5684 =
                           FStar_All.pipe_right
                             (let uu___150_5687 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5687.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5687.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5687.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5687.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5687.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5687.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5687.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5687.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5687.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5684))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5693 =
            FStar_All.pipe_right
              (let uu___151_5696 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5696.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5696.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5696.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5696.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5696.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5696.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5696.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5696.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5696.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5693)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5728 probs =
      match uu____5728 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5758 = rank wl hd1 in
               (match uu____5758 with
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
    match projectee with | UDeferred _0 -> true | uu____5826 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5838 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5850 -> false
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
                        let uu____5883 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5883 with
                        | (k,uu____5887) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5893 -> false)))
            | uu____5894 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5937 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5937 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5940 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5946 =
                     let uu____5947 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5948 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5947
                       uu____5948 in
                   UFailed uu____5946)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5964 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5964 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5982 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5982 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5985 ->
                let uu____5988 =
                  let uu____5989 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5990 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5989
                    uu____5990 msg in
                UFailed uu____5988 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5991,uu____5992) ->
              let uu____5993 =
                let uu____5994 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5995 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5994 uu____5995 in
              failwith uu____5993
          | (FStar_Syntax_Syntax.U_unknown ,uu____5996) ->
              let uu____5997 =
                let uu____5998 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5999 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5998 uu____5999 in
              failwith uu____5997
          | (uu____6000,FStar_Syntax_Syntax.U_bvar uu____6001) ->
              let uu____6002 =
                let uu____6003 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6004 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6003 uu____6004 in
              failwith uu____6002
          | (uu____6005,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6006 =
                let uu____6007 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6008 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6007 uu____6008 in
              failwith uu____6006
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6024 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6024
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6038 = occurs_univ v1 u3 in
              if uu____6038
              then
                let uu____6039 =
                  let uu____6040 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6041 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6040 uu____6041 in
                try_umax_components u11 u21 uu____6039
              else
                (let uu____6043 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6043)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6055 = occurs_univ v1 u3 in
              if uu____6055
              then
                let uu____6056 =
                  let uu____6057 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6058 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6057 uu____6058 in
                try_umax_components u11 u21 uu____6056
              else
                (let uu____6060 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6060)
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
                                        | uu____6935 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6944) ->
                  let uu____6961 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6970  ->
                            match uu___127_6970 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6975 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6975 with
                                      | (u',uu____6986) ->
                                          let uu____7001 =
                                            let uu____7002 = whnf env u' in
                                            uu____7002.FStar_Syntax_Syntax.n in
                                          (match uu____7001 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7006) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7023 -> false))
                                 | uu____7024 -> false)
                            | uu____7026 -> false)) in
                  (match uu____6961 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7047 tps =
                         match uu____7047 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7074 =
                                    let uu____7079 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7079 in
                                  (match uu____7074 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7098 -> None) in
                       let uu____7103 =
                         let uu____7108 =
                           let uu____7112 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7112, []) in
                         make_lower_bound uu____7108 lower_bounds in
                       (match uu____7103 with
                        | None  ->
                            ((let uu____7119 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7119
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
                            ((let uu____7132 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7132
                              then
                                let wl' =
                                  let uu___154_7134 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7134.wl_deferred);
                                    ctr = (uu___154_7134.ctr);
                                    defer_ok = (uu___154_7134.defer_ok);
                                    smt_ok = (uu___154_7134.smt_ok);
                                    tcenv = (uu___154_7134.tcenv)
                                  } in
                                let uu____7135 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7135
                              else ());
                             (let uu____7137 =
                                solve_t env eq_prob
                                  (let uu___155_7138 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7138.wl_deferred);
                                     ctr = (uu___155_7138.ctr);
                                     defer_ok = (uu___155_7138.defer_ok);
                                     smt_ok = (uu___155_7138.smt_ok);
                                     tcenv = (uu___155_7138.tcenv)
                                   }) in
                              match uu____7137 with
                              | Success uu____7140 ->
                                  let wl1 =
                                    let uu___156_7142 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7142.wl_deferred);
                                      ctr = (uu___156_7142.ctr);
                                      defer_ok = (uu___156_7142.defer_ok);
                                      smt_ok = (uu___156_7142.smt_ok);
                                      tcenv = (uu___156_7142.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7144 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7147 -> None))))
              | uu____7148 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7155 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7155
         then
           let uu____7156 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7156
         else ());
        (let uu____7158 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7158 with
         | (u,args) ->
             let uu____7185 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7185 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7216 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7216 with
                    | (h1,args1) ->
                        let uu____7244 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7244 with
                         | (h2,uu____7257) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7276 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7276
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7289 =
                                          let uu____7291 =
                                            let uu____7292 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7292 in
                                          [uu____7291] in
                                        Some uu____7289))
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
                                       (let uu____7314 =
                                          let uu____7316 =
                                            let uu____7317 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7317 in
                                          [uu____7316] in
                                        Some uu____7314))
                                  else None
                              | uu____7325 -> None)) in
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
                             let uu____7391 =
                               let uu____7397 =
                                 let uu____7400 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7400 in
                               (uu____7397, m1) in
                             Some uu____7391)
                    | (uu____7409,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7411)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7443),uu____7444) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7475 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7509) ->
                       let uu____7526 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7535  ->
                                 match uu___128_7535 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7540 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7540 with
                                           | (u',uu____7551) ->
                                               let uu____7566 =
                                                 let uu____7567 = whnf env u' in
                                                 uu____7567.FStar_Syntax_Syntax.n in
                                               (match uu____7566 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7571) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7588 -> false))
                                      | uu____7589 -> false)
                                 | uu____7591 -> false)) in
                       (match uu____7526 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7616 tps =
                              match uu____7616 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7657 =
                                         let uu____7664 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7664 in
                                       (match uu____7657 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7699 -> None) in
                            let uu____7706 =
                              let uu____7713 =
                                let uu____7719 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7719, []) in
                              make_upper_bound uu____7713 upper_bounds in
                            (match uu____7706 with
                             | None  ->
                                 ((let uu____7728 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7728
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
                                 ((let uu____7747 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7747
                                   then
                                     let wl' =
                                       let uu___157_7749 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7749.wl_deferred);
                                         ctr = (uu___157_7749.ctr);
                                         defer_ok = (uu___157_7749.defer_ok);
                                         smt_ok = (uu___157_7749.smt_ok);
                                         tcenv = (uu___157_7749.tcenv)
                                       } in
                                     let uu____7750 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7750
                                   else ());
                                  (let uu____7752 =
                                     solve_t env eq_prob
                                       (let uu___158_7753 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7753.wl_deferred);
                                          ctr = (uu___158_7753.ctr);
                                          defer_ok = (uu___158_7753.defer_ok);
                                          smt_ok = (uu___158_7753.smt_ok);
                                          tcenv = (uu___158_7753.tcenv)
                                        }) in
                                   match uu____7752 with
                                   | Success uu____7755 ->
                                       let wl1 =
                                         let uu___159_7757 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7757.wl_deferred);
                                           ctr = (uu___159_7757.ctr);
                                           defer_ok =
                                             (uu___159_7757.defer_ok);
                                           smt_ok = (uu___159_7757.smt_ok);
                                           tcenv = (uu___159_7757.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7759 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7762 -> None))))
                   | uu____7763 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7828 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7828
                      then
                        let uu____7829 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7829
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7861 = hd1 in
                      let uu____7862 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7861.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7861.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7862
                      } in
                    let hd21 =
                      let uu___161_7866 = hd2 in
                      let uu____7867 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7866.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7866.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7867
                      } in
                    let prob =
                      let uu____7871 =
                        let uu____7874 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7874 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7871 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7882 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7882 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7885 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7885 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7903 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7906 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7903 uu____7906 in
                         ((let uu____7912 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7912
                           then
                             let uu____7913 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7914 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7913 uu____7914
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7929 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7935 = aux scope env [] bs1 bs2 in
              match uu____7935 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7951 = compress_tprob wl problem in
        solve_t' env uu____7951 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7984 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7984 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8001,uu____8002) ->
                   let may_relate head3 =
                     let uu____8017 =
                       let uu____8018 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8018.FStar_Syntax_Syntax.n in
                     match uu____8017 with
                     | FStar_Syntax_Syntax.Tm_name uu____8021 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8022 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8038 -> false in
                   let uu____8039 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8039
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
                                let uu____8056 =
                                  let uu____8057 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8057 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8056 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8059 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8059
                   else giveup env1 "head mismatch" orig
               | (uu____8061,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8069 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8069.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8069.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8069.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8069.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8069.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8069.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8069.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8069.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8070,None ) ->
                   ((let uu____8077 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8077
                     then
                       let uu____8078 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8079 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8080 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8081 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8078
                         uu____8079 uu____8080 uu____8081
                     else ());
                    (let uu____8083 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8083 with
                     | (head11,args1) ->
                         let uu____8109 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8109 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8149 =
                                  let uu____8150 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8151 = args_to_string args1 in
                                  let uu____8152 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8153 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8150 uu____8151 uu____8152
                                    uu____8153 in
                                giveup env1 uu____8149 orig
                              else
                                (let uu____8155 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8158 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8158 = FStar_Syntax_Util.Equal) in
                                 if uu____8155
                                 then
                                   let uu____8159 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8159 with
                                   | USolved wl2 ->
                                       let uu____8161 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8161
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8165 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8165 with
                                    | (base1,refinement1) ->
                                        let uu____8191 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8191 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8245 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8245 with
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
                                                           (fun uu____8255 
                                                              ->
                                                              fun uu____8256 
                                                                ->
                                                                match 
                                                                  (uu____8255,
                                                                    uu____8256)
                                                                with
                                                                | ((a,uu____8266),
                                                                   (a',uu____8268))
                                                                    ->
                                                                    let uu____8273
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
                                                                    uu____8273)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8279 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8279 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8283 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_8316 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8336 = p in
          match uu____8336 with
          | (((u,k),xs,c),ps,(h,uu____8347,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8396 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8396 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8410 = h gs_xs in
                     let uu____8411 =
                       let uu____8418 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8418
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8410 uu____8411 in
                   ((let uu____8449 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8449
                     then
                       let uu____8450 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8451 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8452 = FStar_Syntax_Print.term_to_string im in
                       let uu____8453 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8454 =
                         let uu____8455 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8455
                           (FStar_String.concat ", ") in
                       let uu____8458 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8450 uu____8451 uu____8452 uu____8453
                         uu____8454 uu____8458
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_8476 =
          match uu___129_8476 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8505 = p in
          match uu____8505 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8563 = FStar_List.nth ps i in
              (match uu____8563 with
               | (pi,uu____8566) ->
                   let uu____8571 = FStar_List.nth xs i in
                   (match uu____8571 with
                    | (xi,uu____8578) ->
                        let rec gs k =
                          let uu____8587 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8587 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8639)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8647 = new_uvar r xs k_a in
                                    (match uu____8647 with
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
                                         let uu____8666 = aux subst2 tl1 in
                                         (match uu____8666 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8681 =
                                                let uu____8683 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8683 :: gi_xs' in
                                              let uu____8684 =
                                                let uu____8686 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8686 :: gi_ps' in
                                              (uu____8681, uu____8684))) in
                              aux [] bs in
                        let uu____8689 =
                          let uu____8690 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8690 in
                        if uu____8689
                        then None
                        else
                          (let uu____8693 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8693 with
                           | (g_xs,uu____8700) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8707 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8712 =
                                   let uu____8719 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8719
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8707
                                   uu____8712 in
                               let sub1 =
                                 let uu____8750 =
                                   let uu____8753 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8760 =
                                     let uu____8763 =
                                       FStar_List.map
                                         (fun uu____8769  ->
                                            match uu____8769 with
                                            | (uu____8774,uu____8775,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8763 in
                                   mk_problem (p_scope orig) orig uu____8753
                                     (p_rel orig) uu____8760 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8750 in
                               ((let uu____8785 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8785
                                 then
                                   let uu____8786 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8787 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8786 uu____8787
                                 else ());
                                (let wl2 =
                                   let uu____8790 =
                                     let uu____8792 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8792 in
                                   solve_prob orig uu____8790
                                     [TERM (u, proj)] wl1 in
                                 let uu____8797 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8797))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8821 = lhs in
          match uu____8821 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8844 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8844 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8866 =
                        let uu____8892 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8892) in
                      Some uu____8866
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8975 =
                           let uu____8979 =
                             let uu____8980 = FStar_Syntax_Subst.compress k in
                             uu____8980.FStar_Syntax_Syntax.n in
                           (uu____8979, args) in
                         match uu____8975 with
                         | (uu____8987,[]) ->
                             let uu____8989 =
                               let uu____8995 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8995) in
                             Some uu____8989
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9006,uu____9007) ->
                             let uu____9020 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9020 with
                              | (uv1,uv_args) ->
                                  let uu____9049 =
                                    let uu____9050 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9050.FStar_Syntax_Syntax.n in
                                  (match uu____9049 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9057) ->
                                       let uu____9074 =
                                         pat_vars env [] uv_args in
                                       (match uu____9074 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9088  ->
                                                      let uu____9089 =
                                                        let uu____9090 =
                                                          let uu____9091 =
                                                            let uu____9094 =
                                                              let uu____9095
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9095
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9094 in
                                                          fst uu____9091 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9090 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9089)) in
                                            let c1 =
                                              let uu____9101 =
                                                let uu____9102 =
                                                  let uu____9105 =
                                                    let uu____9106 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9106
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9105 in
                                                fst uu____9102 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9101 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9115 =
                                                let uu____9122 =
                                                  let uu____9128 =
                                                    let uu____9129 =
                                                      let uu____9132 =
                                                        let uu____9133 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9133
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9132 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9129 in
                                                  FStar_Util.Inl uu____9128 in
                                                Some uu____9122 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9115 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9153 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9156,uu____9157)
                             ->
                             let uu____9169 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9169 with
                              | (uv1,uv_args) ->
                                  let uu____9198 =
                                    let uu____9199 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9199.FStar_Syntax_Syntax.n in
                                  (match uu____9198 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9206) ->
                                       let uu____9223 =
                                         pat_vars env [] uv_args in
                                       (match uu____9223 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9237  ->
                                                      let uu____9238 =
                                                        let uu____9239 =
                                                          let uu____9240 =
                                                            let uu____9243 =
                                                              let uu____9244
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9244
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9243 in
                                                          fst uu____9240 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9239 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9238)) in
                                            let c1 =
                                              let uu____9250 =
                                                let uu____9251 =
                                                  let uu____9254 =
                                                    let uu____9255 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9255
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9254 in
                                                fst uu____9251 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9250 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9264 =
                                                let uu____9271 =
                                                  let uu____9277 =
                                                    let uu____9278 =
                                                      let uu____9281 =
                                                        let uu____9282 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9282
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9281 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9278 in
                                                  FStar_Util.Inl uu____9277 in
                                                Some uu____9271 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9264 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9302 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9307)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9333 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9333
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9352 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9352 with
                                  | (args1,rest) ->
                                      let uu____9368 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9368 with
                                       | (xs2,c2) ->
                                           let uu____9376 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9376
                                             (fun uu____9387  ->
                                                match uu____9387 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9409 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9409 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9455 =
                                        let uu____9458 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9458 in
                                      FStar_All.pipe_right uu____9455
                                        (fun _0_57  -> Some _0_57))
                         | uu____9466 ->
                             let uu____9470 =
                               let uu____9471 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9472 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9473 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9471 uu____9472 uu____9473 in
                             failwith uu____9470 in
                       let uu____9477 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9477
                         (fun uu____9505  ->
                            match uu____9505 with
                            | (xs1,c1) ->
                                let uu____9533 =
                                  let uu____9556 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9556) in
                                Some uu____9533)) in
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
                     let uu____9628 = imitate orig env wl1 st in
                     match uu____9628 with
                     | Failed uu____9633 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9639 = project orig env wl1 i st in
                      match uu____9639 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9646) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9660 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9660 with
                | (hd1,uu____9671) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9686 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9694 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9695 -> true
                     | uu____9710 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9713 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9713
                         then true
                         else
                           ((let uu____9716 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9716
                             then
                               let uu____9717 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9717
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9725 =
                    let uu____9728 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9728 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9725 FStar_Syntax_Free.names in
                let uu____9759 = FStar_Util.set_is_empty fvs_hd in
                if uu____9759
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9768 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9768 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9776 =
                            let uu____9777 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9777 in
                          giveup_or_defer1 orig uu____9776
                        else
                          (let uu____9779 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9779
                           then
                             let uu____9780 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9780
                              then
                                let uu____9781 = subterms args_lhs in
                                imitate' orig env wl1 uu____9781
                              else
                                ((let uu____9785 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9785
                                  then
                                    let uu____9786 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9787 = names_to_string fvs1 in
                                    let uu____9788 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9786 uu____9787 uu____9788
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9793 ->
                                        let uu____9794 = sn_binders env vars in
                                        u_abs k_uv uu____9794 t21 in
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
                               (let uu____9803 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9803
                                then
                                  ((let uu____9805 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9805
                                    then
                                      let uu____9806 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9807 = names_to_string fvs1 in
                                      let uu____9808 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9806 uu____9807 uu____9808
                                    else ());
                                   (let uu____9810 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9810
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
                     (let uu____9821 =
                        let uu____9822 = FStar_Syntax_Free.names t1 in
                        check_head uu____9822 t2 in
                      if uu____9821
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9826 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9826
                          then
                            let uu____9827 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9827
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9830 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9830 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9872 =
               match uu____9872 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____9903 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____9903 with
                    | (all_formals,uu____9914) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10006  ->
                                        match uu____10006 with
                                        | (x,imp) ->
                                            let uu____10013 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10013, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10021 = FStar_Syntax_Util.type_u () in
                                match uu____10021 with
                                | (t1,uu____10025) ->
                                    let uu____10026 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10026 in
                              let uu____10029 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10029 with
                               | (t',tm_u1) ->
                                   let uu____10036 = destruct_flex_t t' in
                                   (match uu____10036 with
                                    | (uu____10058,u1,k11,uu____10061) ->
                                        let sol =
                                          let uu____10093 =
                                            let uu____10098 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10098) in
                                          TERM uu____10093 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10162 = pat_var_opt env pat_args hd1 in
                              (match uu____10162 with
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
                                              (fun uu____10191  ->
                                                 match uu____10191 with
                                                 | (x,uu____10195) ->
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
                                      let uu____10201 =
                                        let uu____10202 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10202 in
                                      if uu____10201
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10206 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10206 formals1
                                           tl1)))
                          | uu____10212 -> failwith "Impossible" in
                        let uu____10223 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10223 all_formals args) in
             let solve_both_pats wl1 uu____10263 uu____10264 r =
               match (uu____10263, uu____10264) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10378 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10378
                   then
                     let uu____10379 = solve_prob orig None [] wl1 in
                     solve env uu____10379
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10394 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10394
                       then
                         let uu____10395 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10396 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10397 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10398 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10399 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10395 uu____10396 uu____10397 uu____10398
                           uu____10399
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10441 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10441 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10449 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10449 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10479 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10479 in
                                  let uu____10482 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10482 k3)
                           else
                             (let uu____10485 =
                                let uu____10486 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10487 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10488 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10486 uu____10487 uu____10488 in
                              failwith uu____10485) in
                       let uu____10489 =
                         let uu____10495 =
                           let uu____10503 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10503 in
                         match uu____10495 with
                         | (bs,k1') ->
                             let uu____10521 =
                               let uu____10529 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10529 in
                             (match uu____10521 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10550 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10550 in
                                  let uu____10555 =
                                    let uu____10558 =
                                      let uu____10559 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10559.FStar_Syntax_Syntax.n in
                                    let uu____10562 =
                                      let uu____10563 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10563.FStar_Syntax_Syntax.n in
                                    (uu____10558, uu____10562) in
                                  (match uu____10555 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10571,uu____10572) ->
                                       (k1', [sub_prob])
                                   | (uu____10576,FStar_Syntax_Syntax.Tm_type
                                      uu____10577) -> (k2', [sub_prob])
                                   | uu____10581 ->
                                       let uu____10584 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10584 with
                                        | (t,uu____10593) ->
                                            let uu____10594 = new_uvar r zs t in
                                            (match uu____10594 with
                                             | (k_zs,uu____10603) ->
                                                 let kprob =
                                                   let uu____10605 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10605 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10489 with
                       | (k_u',sub_probs) ->
                           let uu____10619 =
                             let uu____10627 =
                               let uu____10628 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10628 in
                             let uu____10633 =
                               let uu____10636 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10636 in
                             let uu____10639 =
                               let uu____10642 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10642 in
                             (uu____10627, uu____10633, uu____10639) in
                           (match uu____10619 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10661 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10661 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10673 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10673
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10677 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10677 with
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
             let solve_one_pat uu____10709 uu____10710 =
               match (uu____10709, uu____10710) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10774 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10774
                     then
                       let uu____10775 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10776 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10775 uu____10776
                     else ());
                    (let uu____10778 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10778
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10785  ->
                              fun uu____10786  ->
                                match (uu____10785, uu____10786) with
                                | ((a,uu____10796),(t21,uu____10798)) ->
                                    let uu____10803 =
                                      let uu____10806 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10806
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10803
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10810 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10810 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10820 = occurs_check env wl (u1, k1) t21 in
                        match uu____10820 with
                        | (occurs_ok,uu____10825) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10830 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10830
                            then
                              let sol =
                                let uu____10832 =
                                  let uu____10837 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10837) in
                                TERM uu____10832 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10842 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10842
                               then
                                 let uu____10843 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10843 with
                                 | (sol,(uu____10853,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10863 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10863
                                       then
                                         let uu____10864 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10864
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10869 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10871 = lhs in
             match uu____10871 with
             | (t1,u1,k1,args1) ->
                 let uu____10876 = rhs in
                 (match uu____10876 with
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
                       | uu____10902 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10908 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10908 with
                              | (sol,uu____10915) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10918 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10918
                                    then
                                      let uu____10919 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10919
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10924 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10926 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10926
        then
          let uu____10927 = solve_prob orig None [] wl in
          solve env uu____10927
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10931 = FStar_Util.physical_equality t1 t2 in
           if uu____10931
           then
             let uu____10932 = solve_prob orig None [] wl in
             solve env uu____10932
           else
             ((let uu____10935 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10935
               then
                 let uu____10936 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10936
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10939,uu____10940) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10941,FStar_Syntax_Syntax.Tm_bvar uu____10942) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_10982 =
                     match uu___130_10982 with
                     | [] -> c
                     | bs ->
                         let uu____10996 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10996 in
                   let uu____11006 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11006 with
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
                                   let uu____11092 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11092
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11094 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11094))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11171 =
                     match uu___131_11171 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11206 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11206 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11289 =
                                   let uu____11292 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11293 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11292
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11293 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11289))
               | (FStar_Syntax_Syntax.Tm_abs uu____11296,uu____11297) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11320 -> true
                     | uu____11335 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11363 =
                     let uu____11374 = maybe_eta t1 in
                     let uu____11379 = maybe_eta t2 in
                     (uu____11374, uu____11379) in
                   (match uu____11363 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11410 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11410.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11410.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11410.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11410.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11410.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11410.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11410.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11410.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11429 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11429
                        then
                          let uu____11430 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11430 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11451 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11451
                        then
                          let uu____11452 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11452 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11457 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11468,FStar_Syntax_Syntax.Tm_abs uu____11469) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11492 -> true
                     | uu____11507 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11535 =
                     let uu____11546 = maybe_eta t1 in
                     let uu____11551 = maybe_eta t2 in
                     (uu____11546, uu____11551) in
                   (match uu____11535 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11582 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11582.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11582.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11582.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11582.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11582.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11582.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11582.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11582.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11601 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11601
                        then
                          let uu____11602 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11602 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11623 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11623
                        then
                          let uu____11624 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11624 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11629 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11640,FStar_Syntax_Syntax.Tm_refine uu____11641) ->
                   let uu____11650 = as_refinement env wl t1 in
                   (match uu____11650 with
                    | (x1,phi1) ->
                        let uu____11655 = as_refinement env wl t2 in
                        (match uu____11655 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11661 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11661 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11694 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11694
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11698 =
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
                                 let uu____11704 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11704 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11711 =
                                   let uu____11714 =
                                     let uu____11715 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11715 :: (p_scope orig) in
                                   mk_problem uu____11714 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11711 in
                               let uu____11718 =
                                 solve env1
                                   (let uu___165_11719 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_11719.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_11719.smt_ok);
                                      tcenv = (uu___165_11719.tcenv)
                                    }) in
                               (match uu____11718 with
                                | Failed uu____11723 -> fallback ()
                                | Success uu____11726 ->
                                    let guard =
                                      let uu____11730 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11733 =
                                        let uu____11734 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11734
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11730
                                        uu____11733 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___166_11741 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_11741.attempting);
                                        wl_deferred =
                                          (uu___166_11741.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_11741.defer_ok);
                                        smt_ok = (uu___166_11741.smt_ok);
                                        tcenv = (uu___166_11741.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11743,FStar_Syntax_Syntax.Tm_uvar uu____11744) ->
                   let uu____11765 = destruct_flex_t t1 in
                   let uu____11766 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11765 uu____11766
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11767;
                     FStar_Syntax_Syntax.tk = uu____11768;
                     FStar_Syntax_Syntax.pos = uu____11769;
                     FStar_Syntax_Syntax.vars = uu____11770;_},uu____11771),FStar_Syntax_Syntax.Tm_uvar
                  uu____11772) ->
                   let uu____11807 = destruct_flex_t t1 in
                   let uu____11808 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11807 uu____11808
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11809,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11810;
                     FStar_Syntax_Syntax.tk = uu____11811;
                     FStar_Syntax_Syntax.pos = uu____11812;
                     FStar_Syntax_Syntax.vars = uu____11813;_},uu____11814))
                   ->
                   let uu____11849 = destruct_flex_t t1 in
                   let uu____11850 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11849 uu____11850
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11851;
                     FStar_Syntax_Syntax.tk = uu____11852;
                     FStar_Syntax_Syntax.pos = uu____11853;
                     FStar_Syntax_Syntax.vars = uu____11854;_},uu____11855),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11856;
                     FStar_Syntax_Syntax.tk = uu____11857;
                     FStar_Syntax_Syntax.pos = uu____11858;
                     FStar_Syntax_Syntax.vars = uu____11859;_},uu____11860))
                   ->
                   let uu____11909 = destruct_flex_t t1 in
                   let uu____11910 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11909 uu____11910
               | (FStar_Syntax_Syntax.Tm_uvar uu____11911,uu____11912) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11923 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11923 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11927;
                     FStar_Syntax_Syntax.tk = uu____11928;
                     FStar_Syntax_Syntax.pos = uu____11929;
                     FStar_Syntax_Syntax.vars = uu____11930;_},uu____11931),uu____11932)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11957 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11957 t2 wl
               | (uu____11961,FStar_Syntax_Syntax.Tm_uvar uu____11962) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11973,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11974;
                     FStar_Syntax_Syntax.tk = uu____11975;
                     FStar_Syntax_Syntax.pos = uu____11976;
                     FStar_Syntax_Syntax.vars = uu____11977;_},uu____11978))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12003,FStar_Syntax_Syntax.Tm_type uu____12004) ->
                   solve_t' env
                     (let uu___167_12015 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12015.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12015.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12015.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12015.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12015.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12015.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12015.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12015.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12015.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12016;
                     FStar_Syntax_Syntax.tk = uu____12017;
                     FStar_Syntax_Syntax.pos = uu____12018;
                     FStar_Syntax_Syntax.vars = uu____12019;_},uu____12020),FStar_Syntax_Syntax.Tm_type
                  uu____12021) ->
                   solve_t' env
                     (let uu___167_12046 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12046.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12046.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12046.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12046.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12046.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12046.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12046.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12046.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12046.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12047,FStar_Syntax_Syntax.Tm_arrow uu____12048) ->
                   solve_t' env
                     (let uu___167_12066 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12066.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12066.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12066.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12066.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12066.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12066.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12066.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12066.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12066.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12067;
                     FStar_Syntax_Syntax.tk = uu____12068;
                     FStar_Syntax_Syntax.pos = uu____12069;
                     FStar_Syntax_Syntax.vars = uu____12070;_},uu____12071),FStar_Syntax_Syntax.Tm_arrow
                  uu____12072) ->
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
               | (FStar_Syntax_Syntax.Tm_uvar uu____12105,uu____12106) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12119 =
                        let uu____12120 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12120 in
                      if uu____12119
                      then
                        let uu____12121 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_12124 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12124.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12124.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12124.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12124.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12124.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12124.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12124.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12124.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12124.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12125 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12121 uu____12125 t2
                          wl
                      else
                        (let uu____12130 = base_and_refinement env wl t2 in
                         match uu____12130 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12160 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_12163 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12163.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12163.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12163.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12163.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12163.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12163.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12163.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12163.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12163.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12164 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12160
                                    uu____12164 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12179 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12179.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12179.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12182 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12182 in
                                  let guard =
                                    let uu____12190 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12190
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12196;
                     FStar_Syntax_Syntax.tk = uu____12197;
                     FStar_Syntax_Syntax.pos = uu____12198;
                     FStar_Syntax_Syntax.vars = uu____12199;_},uu____12200),uu____12201)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12228 =
                        let uu____12229 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12229 in
                      if uu____12228
                      then
                        let uu____12230 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_12233 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12233.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12233.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12233.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12233.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12233.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12233.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12233.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12233.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12233.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12234 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12230 uu____12234 t2
                          wl
                      else
                        (let uu____12239 = base_and_refinement env wl t2 in
                         match uu____12239 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12269 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_12272 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12272.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12272.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12272.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12272.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12272.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12272.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12272.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12272.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12272.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12273 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12269
                                    uu____12273 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12288 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12288.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12288.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12291 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12291 in
                                  let guard =
                                    let uu____12299 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12299
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12305,FStar_Syntax_Syntax.Tm_uvar uu____12306) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12318 = base_and_refinement env wl t1 in
                      match uu____12318 with
                      | (t_base,uu____12329) ->
                          solve_t env
                            (let uu___171_12344 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12344.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12344.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12344.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12344.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12344.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12344.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12344.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12344.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12347,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12348;
                     FStar_Syntax_Syntax.tk = uu____12349;
                     FStar_Syntax_Syntax.pos = uu____12350;
                     FStar_Syntax_Syntax.vars = uu____12351;_},uu____12352))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12378 = base_and_refinement env wl t1 in
                      match uu____12378 with
                      | (t_base,uu____12389) ->
                          solve_t env
                            (let uu___171_12404 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12404.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12404.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12404.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12404.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12404.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12404.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12404.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12404.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12407,uu____12408) ->
                   let t21 =
                     let uu____12416 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12416 in
                   solve_t env
                     (let uu___172_12429 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_12429.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_12429.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_12429.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_12429.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_12429.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_12429.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_12429.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_12429.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_12429.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12430,FStar_Syntax_Syntax.Tm_refine uu____12431) ->
                   let t11 =
                     let uu____12439 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12439 in
                   solve_t env
                     (let uu___173_12452 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12452.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12452.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_12452.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_12452.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12452.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12452.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12452.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12452.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12452.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12455,uu____12456) ->
                   let head1 =
                     let uu____12474 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12474 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12505 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12505 FStar_Pervasives.fst in
                   let uu____12533 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12533
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12542 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12542
                      then
                        let guard =
                          let uu____12549 =
                            let uu____12550 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12550 = FStar_Syntax_Util.Equal in
                          if uu____12549
                          then None
                          else
                            (let uu____12553 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12553) in
                        let uu____12555 = solve_prob orig guard [] wl in
                        solve env uu____12555
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12558,uu____12559) ->
                   let head1 =
                     let uu____12567 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12567 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12598 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12598 FStar_Pervasives.fst in
                   let uu____12626 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12626
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12635 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12635
                      then
                        let guard =
                          let uu____12642 =
                            let uu____12643 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12643 = FStar_Syntax_Util.Equal in
                          if uu____12642
                          then None
                          else
                            (let uu____12646 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12646) in
                        let uu____12648 = solve_prob orig guard [] wl in
                        solve env uu____12648
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12651,uu____12652) ->
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
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12735) in
                        let uu____12737 = solve_prob orig guard [] wl in
                        solve env uu____12737
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12740,uu____12741) ->
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
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12824) in
                        let uu____12826 = solve_prob orig guard [] wl in
                        solve env uu____12826
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12829,uu____12830) ->
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
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____12913) in
                        let uu____12915 = solve_prob orig guard [] wl in
                        solve env uu____12915
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12918,uu____12919) ->
                   let head1 =
                     let uu____12932 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12932 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12963 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12963 FStar_Pervasives.fst in
                   let uu____12991 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12991
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13000 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13000
                      then
                        let guard =
                          let uu____13007 =
                            let uu____13008 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13008 = FStar_Syntax_Util.Equal in
                          if uu____13007
                          then None
                          else
                            (let uu____13011 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____13011) in
                        let uu____13013 = solve_prob orig guard [] wl in
                        solve env uu____13013
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13016,FStar_Syntax_Syntax.Tm_match uu____13017) ->
                   let head1 =
                     let uu____13035 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13035 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13066 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13066 FStar_Pervasives.fst in
                   let uu____13094 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13094
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13103 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13103
                      then
                        let guard =
                          let uu____13110 =
                            let uu____13111 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13111 = FStar_Syntax_Util.Equal in
                          if uu____13110
                          then None
                          else
                            (let uu____13114 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____13114) in
                        let uu____13116 = solve_prob orig guard [] wl in
                        solve env uu____13116
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13119,FStar_Syntax_Syntax.Tm_uinst uu____13120) ->
                   let head1 =
                     let uu____13128 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13128 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13159 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13159 FStar_Pervasives.fst in
                   let uu____13187 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13187
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13196 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13196
                      then
                        let guard =
                          let uu____13203 =
                            let uu____13204 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13204 = FStar_Syntax_Util.Equal in
                          if uu____13203
                          then None
                          else
                            (let uu____13207 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13207) in
                        let uu____13209 = solve_prob orig guard [] wl in
                        solve env uu____13209
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13212,FStar_Syntax_Syntax.Tm_name uu____13213) ->
                   let head1 =
                     let uu____13217 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13217 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13248 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13248 FStar_Pervasives.fst in
                   let uu____13276 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13276
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13285 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13285
                      then
                        let guard =
                          let uu____13292 =
                            let uu____13293 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13293 = FStar_Syntax_Util.Equal in
                          if uu____13292
                          then None
                          else
                            (let uu____13296 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13296) in
                        let uu____13298 = solve_prob orig guard [] wl in
                        solve env uu____13298
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13301,FStar_Syntax_Syntax.Tm_constant uu____13302) ->
                   let head1 =
                     let uu____13306 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13306 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13337 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13337 FStar_Pervasives.fst in
                   let uu____13365 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13365
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13374 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13374
                      then
                        let guard =
                          let uu____13381 =
                            let uu____13382 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13382 = FStar_Syntax_Util.Equal in
                          if uu____13381
                          then None
                          else
                            (let uu____13385 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13385) in
                        let uu____13387 = solve_prob orig guard [] wl in
                        solve env uu____13387
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13390,FStar_Syntax_Syntax.Tm_fvar uu____13391) ->
                   let head1 =
                     let uu____13395 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13395 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13426 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13426 FStar_Pervasives.fst in
                   let uu____13454 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13454
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13463 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13463
                      then
                        let guard =
                          let uu____13470 =
                            let uu____13471 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13471 = FStar_Syntax_Util.Equal in
                          if uu____13470
                          then None
                          else
                            (let uu____13474 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13474) in
                        let uu____13476 = solve_prob orig guard [] wl in
                        solve env uu____13476
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13479,FStar_Syntax_Syntax.Tm_app uu____13480) ->
                   let head1 =
                     let uu____13493 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13493 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13524 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13524 FStar_Pervasives.fst in
                   let uu____13552 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13552
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13561 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13561
                      then
                        let guard =
                          let uu____13568 =
                            let uu____13569 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13569 = FStar_Syntax_Util.Equal in
                          if uu____13568
                          then None
                          else
                            (let uu____13572 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13572) in
                        let uu____13574 = solve_prob orig guard [] wl in
                        solve env uu____13574
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13578,uu____13579),uu____13580) ->
                   solve_t' env
                     (let uu___174_13609 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_13609.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_13609.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_13609.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_13609.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_13609.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_13609.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_13609.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_13609.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_13609.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13612,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13614,uu____13615)) ->
                   solve_t' env
                     (let uu___175_13644 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13644.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_13644.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13644.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_13644.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13644.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13644.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13644.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13644.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13644.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13645,uu____13646) ->
                   let uu____13654 =
                     let uu____13655 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13656 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13655
                       uu____13656 in
                   failwith uu____13654
               | (FStar_Syntax_Syntax.Tm_meta uu____13657,uu____13658) ->
                   let uu____13663 =
                     let uu____13664 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13665 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13664
                       uu____13665 in
                   failwith uu____13663
               | (FStar_Syntax_Syntax.Tm_delayed uu____13666,uu____13667) ->
                   let uu____13688 =
                     let uu____13689 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13690 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13689
                       uu____13690 in
                   failwith uu____13688
               | (uu____13691,FStar_Syntax_Syntax.Tm_meta uu____13692) ->
                   let uu____13697 =
                     let uu____13698 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13699 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13698
                       uu____13699 in
                   failwith uu____13697
               | (uu____13700,FStar_Syntax_Syntax.Tm_delayed uu____13701) ->
                   let uu____13722 =
                     let uu____13723 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13724 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13723
                       uu____13724 in
                   failwith uu____13722
               | (uu____13725,FStar_Syntax_Syntax.Tm_let uu____13726) ->
                   let uu____13734 =
                     let uu____13735 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13736 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13735
                       uu____13736 in
                   failwith uu____13734
               | uu____13737 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13769 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13769
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13777  ->
                  fun uu____13778  ->
                    match (uu____13777, uu____13778) with
                    | ((a1,uu____13788),(a2,uu____13790)) ->
                        let uu____13795 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13795)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13801 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13801 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13821 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13828)::[] -> wp1
              | uu____13841 ->
                  let uu____13847 =
                    let uu____13848 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13848 in
                  failwith uu____13847 in
            let uu____13851 =
              let uu____13857 =
                let uu____13858 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13858 in
              [uu____13857] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13851;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13859 = lift_c1 () in solve_eq uu____13859 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13863  ->
                       match uu___132_13863 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13864 -> false)) in
             let uu____13865 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13889)::uu____13890,(wp2,uu____13892)::uu____13893)
                   -> (wp1, wp2)
               | uu____13934 ->
                   let uu____13947 =
                     let uu____13948 =
                       let uu____13951 =
                         let uu____13952 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13953 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13952 uu____13953 in
                       (uu____13951, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13948 in
                   raise uu____13947 in
             match uu____13865 with
             | (wpc1,wpc2) ->
                 let uu____13970 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13970
                 then
                   let uu____13973 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13973 wl
                 else
                   (let uu____13977 =
                      let uu____13981 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____13981 in
                    match uu____13977 with
                    | (c2_decl,qualifiers) ->
                        let uu____13993 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____13993
                        then
                          let c1_repr =
                            let uu____13996 =
                              let uu____13997 =
                                let uu____13998 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____13998 in
                              let uu____13999 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13997 uu____13999 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13996 in
                          let c2_repr =
                            let uu____14001 =
                              let uu____14002 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14003 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14002 uu____14003 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14001 in
                          let prob =
                            let uu____14005 =
                              let uu____14008 =
                                let uu____14009 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14010 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14009
                                  uu____14010 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14008 in
                            FStar_TypeChecker_Common.TProb uu____14005 in
                          let wl1 =
                            let uu____14012 =
                              let uu____14014 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14014 in
                            solve_prob orig uu____14012 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14021 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14021
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14023 =
                                     let uu____14026 =
                                       let uu____14027 =
                                         let uu____14037 =
                                           let uu____14038 =
                                             let uu____14039 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14039] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14038 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14040 =
                                           let uu____14042 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14043 =
                                             let uu____14045 =
                                               let uu____14046 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14046 in
                                             [uu____14045] in
                                           uu____14042 :: uu____14043 in
                                         (uu____14037, uu____14040) in
                                       FStar_Syntax_Syntax.Tm_app uu____14027 in
                                     FStar_Syntax_Syntax.mk uu____14026 in
                                   uu____14023
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14057 =
                                    let uu____14060 =
                                      let uu____14061 =
                                        let uu____14071 =
                                          let uu____14072 =
                                            let uu____14073 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14073] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14072 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14074 =
                                          let uu____14076 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14077 =
                                            let uu____14079 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14080 =
                                              let uu____14082 =
                                                let uu____14083 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14083 in
                                              [uu____14082] in
                                            uu____14079 :: uu____14080 in
                                          uu____14076 :: uu____14077 in
                                        (uu____14071, uu____14074) in
                                      FStar_Syntax_Syntax.Tm_app uu____14061 in
                                    FStar_Syntax_Syntax.mk uu____14060 in
                                  uu____14057
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14094 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14094 in
                           let wl1 =
                             let uu____14100 =
                               let uu____14102 =
                                 let uu____14105 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14105 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____14102 in
                             solve_prob orig uu____14100 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14115 = FStar_Util.physical_equality c1 c2 in
        if uu____14115
        then
          let uu____14116 = solve_prob orig None [] wl in
          solve env uu____14116
        else
          ((let uu____14119 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14119
            then
              let uu____14120 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14121 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14120
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14121
            else ());
           (let uu____14123 =
              let uu____14126 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14127 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14126, uu____14127) in
            match uu____14123 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14131),FStar_Syntax_Syntax.Total
                    (t2,uu____14133)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14146 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14146 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14149,FStar_Syntax_Syntax.Total uu____14150) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14162),FStar_Syntax_Syntax.Total
                    (t2,uu____14164)) ->
                     let uu____14177 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14177 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14181),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14183)) ->
                     let uu____14196 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14196 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14200),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14202)) ->
                     let uu____14215 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14215 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14218,FStar_Syntax_Syntax.Comp uu____14219) ->
                     let uu____14225 =
                       let uu___176_14228 = problem in
                       let uu____14231 =
                         let uu____14232 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14232 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14228.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14231;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14228.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14228.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14228.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14228.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14228.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14228.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14228.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14228.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14225 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14233,FStar_Syntax_Syntax.Comp uu____14234) ->
                     let uu____14240 =
                       let uu___176_14243 = problem in
                       let uu____14246 =
                         let uu____14247 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14247 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14243.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14246;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14243.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14243.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14243.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14243.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14243.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14243.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14243.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14243.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14240 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14248,FStar_Syntax_Syntax.GTotal uu____14249) ->
                     let uu____14255 =
                       let uu___177_14258 = problem in
                       let uu____14261 =
                         let uu____14262 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14262 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14258.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14258.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14258.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14261;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14258.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14258.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14258.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14258.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14258.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14258.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14255 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14263,FStar_Syntax_Syntax.Total uu____14264) ->
                     let uu____14270 =
                       let uu___177_14273 = problem in
                       let uu____14276 =
                         let uu____14277 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14277 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14273.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14273.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14273.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14276;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14273.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14273.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14273.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14273.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14273.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14273.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14270 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14278,FStar_Syntax_Syntax.Comp uu____14279) ->
                     let uu____14280 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14280
                     then
                       let uu____14281 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14281 wl
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
                           (let uu____14291 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14291
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14293 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14293 with
                            | None  ->
                                let uu____14295 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14296 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14296) in
                                if uu____14295
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
                                  (let uu____14299 =
                                     let uu____14300 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14301 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14300 uu____14301 in
                                   giveup env uu____14299 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14306 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14322  ->
              match uu____14322 with
              | (uu____14329,uu____14330,u,uu____14332,uu____14333,uu____14334)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14306 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14352 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14352 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14362 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14374  ->
                match uu____14374 with
                | (u1,u2) ->
                    let uu____14379 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14380 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14379 uu____14380)) in
      FStar_All.pipe_right uu____14362 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14392,[])) -> "{}"
      | uu____14405 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14415 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14415
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14418 =
              FStar_List.map
                (fun uu____14422  ->
                   match uu____14422 with
                   | (uu____14425,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14418 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14429 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14429 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14467 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14467
    then
      let uu____14468 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14469 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14468
        (rel_to_string rel) uu____14469
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
            let uu____14489 =
              let uu____14491 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14491 in
            FStar_Syntax_Syntax.new_bv uu____14489 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14497 =
              let uu____14499 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14499 in
            let uu____14501 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14497 uu____14501 in
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
          let uu____14524 = FStar_Options.eager_inference () in
          if uu____14524
          then
            let uu___178_14525 = probs in
            {
              attempting = (uu___178_14525.attempting);
              wl_deferred = (uu___178_14525.wl_deferred);
              ctr = (uu___178_14525.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14525.smt_ok);
              tcenv = (uu___178_14525.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14536 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14536
              then
                let uu____14537 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14537
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
          ((let uu____14547 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14547
            then
              let uu____14548 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14548
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14552 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14552
             then
               let uu____14553 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14553
             else ());
            (let f2 =
               let uu____14556 =
                 let uu____14557 = FStar_Syntax_Util.unmeta f1 in
                 uu____14557.FStar_Syntax_Syntax.n in
               match uu____14556 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14561 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_14562 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14562.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14562.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14562.FStar_TypeChecker_Env.implicits)
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
            let uu____14577 =
              let uu____14578 =
                let uu____14579 =
                  let uu____14580 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14580
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14579;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14578 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14577
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14613 =
        let uu____14614 =
          let uu____14615 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14615
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14614;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14613
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
          (let uu____14641 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14641
           then
             let uu____14642 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14643 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14642
               uu____14643
           else ());
          (let prob =
             let uu____14646 =
               let uu____14649 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14649 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14646 in
           let g =
             let uu____14654 =
               let uu____14656 = singleton' env prob smt_ok in
               solve_and_commit env uu____14656 (fun uu____14657  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14654 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14671 = try_teq true env t1 t2 in
        match uu____14671 with
        | None  ->
            let uu____14673 =
              let uu____14674 =
                let uu____14677 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14678 = FStar_TypeChecker_Env.get_range env in
                (uu____14677, uu____14678) in
              FStar_Errors.Error uu____14674 in
            raise uu____14673
        | Some g ->
            ((let uu____14681 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14681
              then
                let uu____14682 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14683 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14684 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14682
                  uu____14683 uu____14684
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
          (let uu____14700 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14700
           then
             let uu____14701 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14702 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14701
               uu____14702
           else ());
          (let uu____14704 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14704 with
           | (prob,x) ->
               let g =
                 let uu____14712 =
                   let uu____14714 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14714
                     (fun uu____14715  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14712 in
               ((let uu____14721 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14721
                 then
                   let uu____14722 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14723 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14724 =
                     let uu____14725 = FStar_Util.must g in
                     guard_to_string env uu____14725 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14722 uu____14723 uu____14724
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
          let uu____14749 = FStar_TypeChecker_Env.get_range env in
          let uu____14750 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14749 uu____14750
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14762 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14762
         then
           let uu____14763 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14764 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14763
             uu____14764
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14769 =
             let uu____14772 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14772 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14769 in
         let uu____14775 =
           let uu____14777 = singleton env prob in
           solve_and_commit env uu____14777 (fun uu____14778  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14775)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14797  ->
        match uu____14797 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14822 =
                 let uu____14823 =
                   let uu____14826 =
                     let uu____14827 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14828 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14827 uu____14828 in
                   let uu____14829 = FStar_TypeChecker_Env.get_range env in
                   (uu____14826, uu____14829) in
                 FStar_Errors.Error uu____14823 in
               raise uu____14822) in
            let equiv1 v1 v' =
              let uu____14837 =
                let uu____14840 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14841 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14840, uu____14841) in
              match uu____14837 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14852 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14866 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14866 with
                      | FStar_Syntax_Syntax.U_unif uu____14870 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14883  ->
                                    match uu____14883 with
                                    | (u,v') ->
                                        let uu____14889 = equiv1 v1 v' in
                                        if uu____14889
                                        then
                                          let uu____14891 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14891 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14901 -> [])) in
            let uu____14904 =
              let wl =
                let uu___180_14907 = empty_worklist env in
                {
                  attempting = (uu___180_14907.attempting);
                  wl_deferred = (uu___180_14907.wl_deferred);
                  ctr = (uu___180_14907.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_14907.smt_ok);
                  tcenv = (uu___180_14907.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14914  ->
                      match uu____14914 with
                      | (lb,v1) ->
                          let uu____14919 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14919 with
                           | USolved wl1 -> ()
                           | uu____14921 -> fail lb v1))) in
            let rec check_ineq uu____14927 =
              match uu____14927 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14934) -> true
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
                      uu____14949,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14951,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14958) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14962,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14967 -> false) in
            let uu____14970 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14976  ->
                      match uu____14976 with
                      | (u,v1) ->
                          let uu____14981 = check_ineq (u, v1) in
                          if uu____14981
                          then true
                          else
                            ((let uu____14984 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____14984
                              then
                                let uu____14985 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____14986 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____14985
                                  uu____14986
                              else ());
                             false))) in
            if uu____14970
            then ()
            else
              ((let uu____14990 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____14990
                then
                  ((let uu____14992 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14992);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14998 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14998))
                else ());
               (let uu____15004 =
                  let uu____15005 =
                    let uu____15008 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15008) in
                  FStar_Errors.Error uu____15005 in
                raise uu____15004))
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
      let fail uu____15041 =
        match uu____15041 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15051 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15051
       then
         let uu____15052 = wl_to_string wl in
         let uu____15053 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15052 uu____15053
       else ());
      (let g1 =
         let uu____15065 = solve_and_commit env wl fail in
         match uu____15065 with
         | Some [] ->
             let uu___181_15072 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15072.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15072.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15072.FStar_TypeChecker_Env.implicits)
             }
         | uu____15075 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15078 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15078.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15078.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15078.FStar_TypeChecker_Env.implicits)
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
            let uu___183_15104 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15104.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15104.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15104.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15105 =
            let uu____15106 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15106 in
          if uu____15105
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15112 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15112
                   then
                     let uu____15113 = FStar_TypeChecker_Env.get_range env in
                     let uu____15114 =
                       let uu____15115 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15115 in
                     FStar_Errors.diag uu____15113 uu____15114
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
                         ((let uu____15124 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15124
                           then
                             let uu____15125 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15126 =
                               let uu____15127 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15127 in
                             FStar_Errors.diag uu____15125 uu____15126
                           else ());
                          (let vcs =
                             let uu____15133 = FStar_Options.use_tactics () in
                             if uu____15133
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15147  ->
                                   match uu____15147 with
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
      let uu____15158 = discharge_guard' None env g false in
      match uu____15158 with
      | Some g1 -> g1
      | None  ->
          let uu____15163 =
            let uu____15164 =
              let uu____15167 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15167) in
            FStar_Errors.Error uu____15164 in
          raise uu____15163
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15174 = discharge_guard' None env g true in
      match uu____15174 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15186 = FStar_Syntax_Unionfind.find u in
      match uu____15186 with | None  -> true | uu____15188 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15201 = acc in
      match uu____15201 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15247 = hd1 in
               (match uu____15247 with
                | (uu____15254,env,u,tm,k,r) ->
                    let uu____15260 = unresolved u in
                    if uu____15260
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15278 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15278
                        then
                          let uu____15279 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15280 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15281 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15279 uu____15280 uu____15281
                        else ());
                       (let uu____15283 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15287 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15287.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15287.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15287.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15287.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15287.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15287.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15287.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15287.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15287.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15287.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15287.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15287.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15287.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15287.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15287.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15287.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15287.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15287.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15287.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15287.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15287.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15287.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15287.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____15283 with
                        | (uu____15288,uu____15289,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15292 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15292.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15292.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15292.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15295 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15299  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15295 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_15314 = g in
    let uu____15315 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15314.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15314.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15314.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15315
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15343 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15343 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15350 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15350
      | (reason,uu____15352,uu____15353,e,t,r)::uu____15357 ->
          let uu____15371 =
            let uu____15372 = FStar_Syntax_Print.term_to_string t in
            let uu____15373 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15372 uu____15373 in
          FStar_Errors.err r uu____15371
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15380 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15380.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15380.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15380.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15398 = try_teq false env t1 t2 in
        match uu____15398 with
        | None  -> false
        | Some g ->
            let uu____15401 = discharge_guard' None env g false in
            (match uu____15401 with
             | Some uu____15405 -> true
             | None  -> false)