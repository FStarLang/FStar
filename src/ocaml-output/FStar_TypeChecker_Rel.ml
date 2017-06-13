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
    | FStar_Syntax_Syntax.Tm_meta uu____1832 ->
        let uu____1837 =
          let uu____1838 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1839 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1838
            uu____1839 in
        failwith uu____1837
    | FStar_Syntax_Syntax.Tm_ascribed uu____1849 ->
        let uu____1867 =
          let uu____1868 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1869 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1868
            uu____1869 in
        failwith uu____1867
    | FStar_Syntax_Syntax.Tm_delayed uu____1879 ->
        let uu____1900 =
          let uu____1901 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1902 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1901
            uu____1902 in
        failwith uu____1900
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1912 =
          let uu____1913 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1914 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1913
            uu____1914 in
        failwith uu____1912 in
  let uu____1924 = whnf env t1 in aux false uu____1924
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1933 =
        let uu____1943 = empty_worklist env in
        base_and_refinement env uu____1943 t in
      FStar_All.pipe_right uu____1933 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1967 = FStar_Syntax_Syntax.null_bv t in
    (uu____1967, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1987 = base_and_refinement env wl t in
  match uu____1987 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2046 =
  match uu____2046 with
  | (t_base,refopt) ->
      let uu____2060 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2060 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2084  ->
      match uu___121_2084 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2088 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2089 =
            let uu____2090 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2090 in
          let uu____2091 =
            let uu____2092 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2092 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2088 uu____2089
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2091
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2096 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2097 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2098 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2096 uu____2097
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2098
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2102 =
      let uu____2104 =
        let uu____2106 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2116  ->
                  match uu____2116 with | (uu____2120,uu____2121,x) -> x)) in
        FStar_List.append wl.attempting uu____2106 in
      FStar_List.map (wl_prob_to_string wl) uu____2104 in
    FStar_All.pipe_right uu____2102 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2139 =
          let uu____2149 =
            let uu____2150 = FStar_Syntax_Subst.compress k in
            uu____2150.FStar_Syntax_Syntax.n in
          match uu____2149 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2191 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2191)
              else
                (let uu____2205 = FStar_Syntax_Util.abs_formals t in
                 match uu____2205 with
                 | (ys',t1,uu____2226) ->
                     let uu____2239 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2239))
          | uu____2260 ->
              let uu____2261 =
                let uu____2267 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2267) in
              ((ys, t), uu____2261) in
        match uu____2139 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2322 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2322 c in
               let uu____2324 =
                 let uu____2331 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2331 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2324)
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
            let uu____2382 = p_guard prob in
            match uu____2382 with
            | (uu____2385,uv) ->
                ((let uu____2388 =
                    let uu____2389 = FStar_Syntax_Subst.compress uv in
                    uu____2389.FStar_Syntax_Syntax.n in
                  match uu____2388 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2413 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2413
                        then
                          let uu____2414 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2415 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2416 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2414
                            uu____2415 uu____2416
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2418 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2421 = wl in
                  {
                    attempting = (uu___144_2421.attempting);
                    wl_deferred = (uu___144_2421.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2421.defer_ok);
                    smt_ok = (uu___144_2421.smt_ok);
                    tcenv = (uu___144_2421.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2434 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2434
         then
           let uu____2435 = FStar_Util.string_of_int pid in
           let uu____2436 =
             let uu____2437 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2437 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2435 uu____2436
         else ());
        commit sol;
        (let uu___145_2442 = wl in
         {
           attempting = (uu___145_2442.attempting);
           wl_deferred = (uu___145_2442.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2442.defer_ok);
           smt_ok = (uu___145_2442.smt_ok);
           tcenv = (uu___145_2442.tcenv)
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
            | (uu____2471,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2479 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2479 in
          (let uu____2485 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2485
           then
             let uu____2486 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2487 =
               let uu____2488 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2488 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2486 uu____2487
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2513 =
    let uu____2517 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2517 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2513
    (FStar_Util.for_some
       (fun uu____2534  ->
          match uu____2534 with
          | (uv,uu____2538) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2571 = occurs wl uk t in Prims.op_Negation uu____2571 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2576 =
         let uu____2577 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2578 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2577 uu____2578 in
       Some uu____2576) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2626 = occurs_check env wl uk t in
  match uu____2626 with
  | (occurs_ok,msg) ->
      let uu____2643 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2643, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2707 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2731  ->
            fun uu____2732  ->
              match (uu____2731, uu____2732) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2775 =
                    let uu____2776 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2776 in
                  if uu____2775
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2790 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2790
                     then
                       let uu____2797 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2797)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2707 with | (isect,uu____2819) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2868  ->
          fun uu____2869  ->
            match (uu____2868, uu____2869) with
            | ((a,uu____2879),(b,uu____2881)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2925 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2931  ->
                match uu____2931 with
                | (b,uu____2935) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2925 then None else Some (a, (snd hd1))
  | uu____2944 -> None
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
            let uu____2987 = pat_var_opt env seen hd1 in
            (match uu____2987 with
             | None  ->
                 ((let uu____2995 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2995
                   then
                     let uu____2996 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2996
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3008 =
      let uu____3009 = FStar_Syntax_Subst.compress t in
      uu____3009.FStar_Syntax_Syntax.n in
    match uu____3008 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3012 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3023;
           FStar_Syntax_Syntax.tk = uu____3024;
           FStar_Syntax_Syntax.pos = uu____3025;
           FStar_Syntax_Syntax.vars = uu____3026;_},uu____3027)
        -> true
    | uu____3052 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3122;
         FStar_Syntax_Syntax.pos = uu____3123;
         FStar_Syntax_Syntax.vars = uu____3124;_},args)
      -> (t, uv, k, args)
  | uu____3171 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3229 = destruct_flex_t t in
  match uu____3229 with
  | (t1,uv,k,args) ->
      let uu____3305 = pat_vars env [] args in
      (match uu____3305 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3367 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3420 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3443 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3447 -> false
let head_match: match_result -> match_result =
  fun uu___122_3450  ->
    match uu___122_3450 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3459 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3472 ->
          let uu____3473 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3473 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3483 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3497 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3503 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3525 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3526 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3527 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3538 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3546 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3563) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3569,uu____3570) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3600) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3615;
             FStar_Syntax_Syntax.index = uu____3616;
             FStar_Syntax_Syntax.sort = t2;_},uu____3618)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3625 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3626 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3627 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3635 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3651 = fv_delta_depth env fv in Some uu____3651
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
            let uu____3670 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3670
            then FullMatch
            else
              (let uu____3672 =
                 let uu____3677 =
                   let uu____3679 = fv_delta_depth env f in Some uu____3679 in
                 let uu____3680 =
                   let uu____3682 = fv_delta_depth env g in Some uu____3682 in
                 (uu____3677, uu____3680) in
               MisMatch uu____3672)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3686),FStar_Syntax_Syntax.Tm_uinst (g,uu____3688)) ->
            let uu____3697 = head_matches env f g in
            FStar_All.pipe_right uu____3697 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3704),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3706)) ->
            let uu____3739 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3739 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3744),FStar_Syntax_Syntax.Tm_refine (y,uu____3746)) ->
            let uu____3755 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3755 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3757),uu____3758) ->
            let uu____3763 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3763 head_match
        | (uu____3764,FStar_Syntax_Syntax.Tm_refine (x,uu____3766)) ->
            let uu____3771 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3771 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3772,FStar_Syntax_Syntax.Tm_type
           uu____3773) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3774,FStar_Syntax_Syntax.Tm_arrow uu____3775) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3791),FStar_Syntax_Syntax.Tm_app (head',uu____3793))
            ->
            let uu____3822 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3822 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3824),uu____3825) ->
            let uu____3840 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3840 head_match
        | (uu____3841,FStar_Syntax_Syntax.Tm_app (head1,uu____3843)) ->
            let uu____3858 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3858 head_match
        | uu____3859 ->
            let uu____3862 =
              let uu____3867 = delta_depth_of_term env t11 in
              let uu____3869 = delta_depth_of_term env t21 in
              (uu____3867, uu____3869) in
            MisMatch uu____3862
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3905 = FStar_Syntax_Util.head_and_args t in
    match uu____3905 with
    | (head1,uu____3917) ->
        let uu____3932 =
          let uu____3933 = FStar_Syntax_Util.un_uinst head1 in
          uu____3933.FStar_Syntax_Syntax.n in
        (match uu____3932 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3938 =
               let uu____3939 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3939 FStar_Option.isSome in
             if uu____3938
             then
               let uu____3953 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3953 (fun _0_38  -> Some _0_38)
             else None
         | uu____3956 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4024) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4034 =
             let uu____4039 = maybe_inline t11 in
             let uu____4041 = maybe_inline t21 in (uu____4039, uu____4041) in
           match uu____4034 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4062,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4072 =
             let uu____4077 = maybe_inline t11 in
             let uu____4079 = maybe_inline t21 in (uu____4077, uu____4079) in
           match uu____4072 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4104 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4104 with
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
        let uu____4119 =
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
             let uu____4127 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4127)) in
        (match uu____4119 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4135 -> fail r
    | uu____4140 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4169 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4199 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4214 = FStar_Syntax_Util.type_u () in
      match uu____4214 with
      | (t,uu____4218) ->
          let uu____4219 = new_uvar r binders t in fst uu____4219
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4228 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4228 FStar_Pervasives.fst
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
        let uu____4270 = head_matches env t1 t' in
        match uu____4270 with
        | MisMatch uu____4271 -> false
        | uu____4276 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4336,imp),T (t2,uu____4339)) -> (t2, imp)
                     | uu____4356 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4396  ->
                    match uu____4396 with
                    | (t2,uu____4404) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4434 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4434 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4487))::tcs2) ->
                       aux
                         (((let uu___146_4509 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4509.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4509.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4519 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_4550 =
                 match uu___123_4550 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4613 = decompose1 [] bs1 in
               (rebuild, matches, uu____4613))
      | uu____4641 ->
          let rebuild uu___124_4646 =
            match uu___124_4646 with
            | [] -> t1
            | uu____4648 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4667  ->
    match uu___125_4667 with
    | T (t,uu____4669) -> t
    | uu____4678 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4681  ->
    match uu___126_4681 with
    | T (t,uu____4683) -> FStar_Syntax_Syntax.as_arg t
    | uu____4692 -> failwith "Impossible"
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
              | (uu____4761,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4780 = new_uvar r scope1 k in
                  (match uu____4780 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4792 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4807 =
                         let uu____4808 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4808 in
                       ((T (gi_xs, mk_kind)), uu____4807))
              | (uu____4817,uu____4818,C uu____4819) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4906 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4917;
                         FStar_Syntax_Syntax.pos = uu____4918;
                         FStar_Syntax_Syntax.vars = uu____4919;_})
                        ->
                        let uu____4934 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4934 with
                         | (T (gi_xs,uu____4950),prob) ->
                             let uu____4960 =
                               let uu____4961 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4961 in
                             (uu____4960, [prob])
                         | uu____4963 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4973;
                         FStar_Syntax_Syntax.pos = uu____4974;
                         FStar_Syntax_Syntax.vars = uu____4975;_})
                        ->
                        let uu____4990 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4990 with
                         | (T (gi_xs,uu____5006),prob) ->
                             let uu____5016 =
                               let uu____5017 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5017 in
                             (uu____5016, [prob])
                         | uu____5019 -> failwith "impossible")
                    | (uu____5025,uu____5026,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5028;
                         FStar_Syntax_Syntax.pos = uu____5029;
                         FStar_Syntax_Syntax.vars = uu____5030;_})
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
                        let uu____5104 =
                          let uu____5109 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5109 FStar_List.unzip in
                        (match uu____5104 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5138 =
                                 let uu____5139 =
                                   let uu____5142 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5142 un_T in
                                 let uu____5143 =
                                   let uu____5149 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5149
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5139;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5143;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5138 in
                             ((C gi_xs), sub_probs))
                    | uu____5154 ->
                        let uu____5161 = sub_prob scope1 args q in
                        (match uu____5161 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4906 with
                   | (tc,probs) ->
                       let uu____5179 =
                         match q with
                         | (Some b,uu____5205,uu____5206) ->
                             let uu____5214 =
                               let uu____5218 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5218 :: args in
                             ((Some b), (b :: scope1), uu____5214)
                         | uu____5236 -> (None, scope1, args) in
                       (match uu____5179 with
                        | (bopt,scope2,args1) ->
                            let uu____5279 = aux scope2 args1 qs2 in
                            (match uu____5279 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5300 =
                                         let uu____5302 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5302 in
                                       FStar_Syntax_Util.mk_conj_l uu____5300
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5315 =
                                         let uu____5317 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5318 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5317 :: uu____5318 in
                                       FStar_Syntax_Util.mk_conj_l uu____5315 in
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
  let uu___147_5371 = p in
  let uu____5374 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5375 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5371.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5374;
    FStar_TypeChecker_Common.relation =
      (uu___147_5371.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5375;
    FStar_TypeChecker_Common.element =
      (uu___147_5371.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5371.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5371.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5371.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5371.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5371.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5385 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5385
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5390 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5404 = compress_prob wl pr in
        FStar_All.pipe_right uu____5404 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5410 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5410 with
           | (lh,uu____5423) ->
               let uu____5438 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5438 with
                | (rh,uu____5451) ->
                    let uu____5466 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5475,FStar_Syntax_Syntax.Tm_uvar uu____5476)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5499,uu____5500)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5513,FStar_Syntax_Syntax.Tm_uvar uu____5514)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5527,uu____5528)
                          ->
                          let uu____5539 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5539 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5579 ->
                                    let rank =
                                      let uu____5586 = is_top_level_prob prob in
                                      if uu____5586
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5588 =
                                      let uu___148_5591 = tp in
                                      let uu____5594 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5591.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5591.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5591.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5594;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5591.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5591.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5591.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5591.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5591.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5591.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5588)))
                      | (uu____5604,FStar_Syntax_Syntax.Tm_uvar uu____5605)
                          ->
                          let uu____5616 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5616 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5656 ->
                                    let uu____5662 =
                                      let uu___149_5667 = tp in
                                      let uu____5670 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5667.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5670;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5667.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5667.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5667.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5667.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5667.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5667.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5667.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5667.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5662)))
                      | (uu____5686,uu____5687) -> (rigid_rigid, tp) in
                    (match uu____5466 with
                     | (rank,tp1) ->
                         let uu____5698 =
                           FStar_All.pipe_right
                             (let uu___150_5701 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5701.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5701.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5701.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5701.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5701.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5701.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5701.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5701.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5701.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5698))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5707 =
            FStar_All.pipe_right
              (let uu___151_5710 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5710.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5710.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5710.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5710.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5710.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5710.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5710.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5710.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5710.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5707)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5742 probs =
      match uu____5742 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5772 = rank wl hd1 in
               (match uu____5772 with
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
    match projectee with | UDeferred _0 -> true | uu____5840 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5852 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5864 -> false
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
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5907 -> false)))
            | uu____5908 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5951 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5951 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5954 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5960 =
                     let uu____5961 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5962 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5961
                       uu____5962 in
                   UFailed uu____5960)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5978 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5978 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5996 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5996 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5999 ->
                let uu____6002 =
                  let uu____6003 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____6004 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6003
                    uu____6004 msg in
                UFailed uu____6002 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6005,uu____6006) ->
              let uu____6007 =
                let uu____6008 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6009 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6008 uu____6009 in
              failwith uu____6007
          | (FStar_Syntax_Syntax.U_unknown ,uu____6010) ->
              let uu____6011 =
                let uu____6012 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6013 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6012 uu____6013 in
              failwith uu____6011
          | (uu____6014,FStar_Syntax_Syntax.U_bvar uu____6015) ->
              let uu____6016 =
                let uu____6017 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6018 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6017 uu____6018 in
              failwith uu____6016
          | (uu____6019,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6020 =
                let uu____6021 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6022 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6021 uu____6022 in
              failwith uu____6020
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6038 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6038
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6052 = occurs_univ v1 u3 in
              if uu____6052
              then
                let uu____6053 =
                  let uu____6054 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6055 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6054 uu____6055 in
                try_umax_components u11 u21 uu____6053
              else
                (let uu____6057 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6057)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6069 = occurs_univ v1 u3 in
              if uu____6069
              then
                let uu____6070 =
                  let uu____6071 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6072 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6071 uu____6072 in
                try_umax_components u11 u21 uu____6070
              else
                (let uu____6074 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6074)
          | (FStar_Syntax_Syntax.U_max uu____6079,uu____6080) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6085 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6085
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6087,FStar_Syntax_Syntax.U_max uu____6088) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6093 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6093
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6095,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6096,FStar_Syntax_Syntax.U_name
             uu____6097) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6098) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6099) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6100,FStar_Syntax_Syntax.U_succ
             uu____6101) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6102,FStar_Syntax_Syntax.U_zero
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
  let uu____6164 = bc1 in
  match uu____6164 with
  | (bs1,mk_cod1) ->
      let uu____6189 = bc2 in
      (match uu____6189 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6236 = FStar_Util.first_N n1 bs in
             match uu____6236 with
             | (bs3,rest) ->
                 let uu____6250 = mk_cod rest in (bs3, uu____6250) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6268 =
               let uu____6272 = mk_cod1 [] in (bs1, uu____6272) in
             let uu____6274 =
               let uu____6278 = mk_cod2 [] in (bs2, uu____6278) in
             (uu____6268, uu____6274)
           else
             if l1 > l2
             then
               (let uu____6300 = curry l2 bs1 mk_cod1 in
                let uu____6307 =
                  let uu____6311 = mk_cod2 [] in (bs2, uu____6311) in
                (uu____6300, uu____6307))
             else
               (let uu____6320 =
                  let uu____6324 = mk_cod1 [] in (bs1, uu____6324) in
                let uu____6326 = curry l1 bs2 mk_cod2 in
                (uu____6320, uu____6326)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6430 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6430
       then
         let uu____6431 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6431
       else ());
      (let uu____6433 = next_prob probs in
       match uu____6433 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6446 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6446.wl_deferred);
               ctr = (uu___152_6446.ctr);
               defer_ok = (uu___152_6446.defer_ok);
               smt_ok = (uu___152_6446.smt_ok);
               tcenv = (uu___152_6446.tcenv)
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
                  let uu____6453 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6453 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6457 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6457 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6461,uu____6462) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6471 ->
                let uu____6476 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6504  ->
                          match uu____6504 with
                          | (c,uu____6509,uu____6510) -> c < probs.ctr)) in
                (match uu____6476 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6532 =
                            FStar_List.map
                              (fun uu____6538  ->
                                 match uu____6538 with
                                 | (uu____6544,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6532
                      | uu____6547 ->
                          let uu____6552 =
                            let uu___153_6553 = probs in
                            let uu____6554 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6563  ->
                                      match uu____6563 with
                                      | (uu____6567,uu____6568,y) -> y)) in
                            {
                              attempting = uu____6554;
                              wl_deferred = rest;
                              ctr = (uu___153_6553.ctr);
                              defer_ok = (uu___153_6553.defer_ok);
                              smt_ok = (uu___153_6553.smt_ok);
                              tcenv = (uu___153_6553.tcenv)
                            } in
                          solve env uu____6552))))
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
            let uu____6575 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6575 with
            | USolved wl1 ->
                let uu____6577 = solve_prob orig None [] wl1 in
                solve env uu____6577
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
                  let uu____6611 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6611 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6614 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6622;
                  FStar_Syntax_Syntax.pos = uu____6623;
                  FStar_Syntax_Syntax.vars = uu____6624;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6627;
                  FStar_Syntax_Syntax.pos = uu____6628;
                  FStar_Syntax_Syntax.vars = uu____6629;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6641,uu____6642) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6647,FStar_Syntax_Syntax.Tm_uinst uu____6648) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6653 -> USolved wl
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
            ((let uu____6661 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6661
              then
                let uu____6662 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6662 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6670 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6670
         then
           let uu____6671 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6671
         else ());
        (let uu____6673 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6673 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6715 = head_matches_delta env () t1 t2 in
               match uu____6715 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6737 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6763 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6772 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6773 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6772, uu____6773)
                          | None  ->
                              let uu____6776 = FStar_Syntax_Subst.compress t1 in
                              let uu____6777 = FStar_Syntax_Subst.compress t2 in
                              (uu____6776, uu____6777) in
                        (match uu____6763 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6799 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6799 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6822 =
                                    let uu____6828 =
                                      let uu____6831 =
                                        let uu____6834 =
                                          let uu____6835 =
                                            let uu____6840 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6840) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6835 in
                                        FStar_Syntax_Syntax.mk uu____6834 in
                                      uu____6831 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6853 =
                                      let uu____6855 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6855] in
                                    (uu____6828, uu____6853) in
                                  Some uu____6822
                              | (uu____6864,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6866)) ->
                                  let uu____6871 =
                                    let uu____6875 =
                                      let uu____6877 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6877] in
                                    (t11, uu____6875) in
                                  Some uu____6871
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6883),uu____6884) ->
                                  let uu____6889 =
                                    let uu____6893 =
                                      let uu____6895 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6895] in
                                    (t21, uu____6893) in
                                  Some uu____6889
                              | uu____6900 ->
                                  let uu____6903 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6903 with
                                   | (head1,uu____6918) ->
                                       let uu____6933 =
                                         let uu____6934 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6934.FStar_Syntax_Syntax.n in
                                       (match uu____6933 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6941;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6943;_}
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
                                        | uu____6952 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6961) ->
                  let uu____6978 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6987  ->
                            match uu___127_6987 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6992 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6992 with
                                      | (u',uu____7003) ->
                                          let uu____7018 =
                                            let uu____7019 = whnf env u' in
                                            uu____7019.FStar_Syntax_Syntax.n in
                                          (match uu____7018 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7023) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7040 -> false))
                                 | uu____7041 -> false)
                            | uu____7043 -> false)) in
                  (match uu____6978 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7064 tps =
                         match uu____7064 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7091 =
                                    let uu____7096 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7096 in
                                  (match uu____7091 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7115 -> None) in
                       let uu____7120 =
                         let uu____7125 =
                           let uu____7129 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7129, []) in
                         make_lower_bound uu____7125 lower_bounds in
                       (match uu____7120 with
                        | None  ->
                            ((let uu____7136 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7136
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
                            ((let uu____7149 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7149
                              then
                                let wl' =
                                  let uu___154_7151 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7151.wl_deferred);
                                    ctr = (uu___154_7151.ctr);
                                    defer_ok = (uu___154_7151.defer_ok);
                                    smt_ok = (uu___154_7151.smt_ok);
                                    tcenv = (uu___154_7151.tcenv)
                                  } in
                                let uu____7152 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7152
                              else ());
                             (let uu____7154 =
                                solve_t env eq_prob
                                  (let uu___155_7155 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7155.wl_deferred);
                                     ctr = (uu___155_7155.ctr);
                                     defer_ok = (uu___155_7155.defer_ok);
                                     smt_ok = (uu___155_7155.smt_ok);
                                     tcenv = (uu___155_7155.tcenv)
                                   }) in
                              match uu____7154 with
                              | Success uu____7157 ->
                                  let wl1 =
                                    let uu___156_7159 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7159.wl_deferred);
                                      ctr = (uu___156_7159.ctr);
                                      defer_ok = (uu___156_7159.defer_ok);
                                      smt_ok = (uu___156_7159.smt_ok);
                                      tcenv = (uu___156_7159.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7161 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7164 -> None))))
              | uu____7165 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7172 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7172
         then
           let uu____7173 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7173
         else ());
        (let uu____7175 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7175 with
         | (u,args) ->
             let uu____7202 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7202 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7233 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7233 with
                    | (h1,args1) ->
                        let uu____7261 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7261 with
                         | (h2,uu____7274) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7293 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7293
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7306 =
                                          let uu____7308 =
                                            let uu____7309 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7309 in
                                          [uu____7308] in
                                        Some uu____7306))
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
                                       (let uu____7331 =
                                          let uu____7333 =
                                            let uu____7334 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7334 in
                                          [uu____7333] in
                                        Some uu____7331))
                                  else None
                              | uu____7342 -> None)) in
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
                             let uu____7408 =
                               let uu____7414 =
                                 let uu____7417 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7417 in
                               (uu____7414, m1) in
                             Some uu____7408)
                    | (uu____7426,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7428)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7460),uu____7461) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7492 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7526) ->
                       let uu____7543 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7552  ->
                                 match uu___128_7552 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7557 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7557 with
                                           | (u',uu____7568) ->
                                               let uu____7583 =
                                                 let uu____7584 = whnf env u' in
                                                 uu____7584.FStar_Syntax_Syntax.n in
                                               (match uu____7583 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7588) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7605 -> false))
                                      | uu____7606 -> false)
                                 | uu____7608 -> false)) in
                       (match uu____7543 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7633 tps =
                              match uu____7633 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7674 =
                                         let uu____7681 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7681 in
                                       (match uu____7674 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7716 -> None) in
                            let uu____7723 =
                              let uu____7730 =
                                let uu____7736 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7736, []) in
                              make_upper_bound uu____7730 upper_bounds in
                            (match uu____7723 with
                             | None  ->
                                 ((let uu____7745 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7745
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
                                 ((let uu____7764 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7764
                                   then
                                     let wl' =
                                       let uu___157_7766 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7766.wl_deferred);
                                         ctr = (uu___157_7766.ctr);
                                         defer_ok = (uu___157_7766.defer_ok);
                                         smt_ok = (uu___157_7766.smt_ok);
                                         tcenv = (uu___157_7766.tcenv)
                                       } in
                                     let uu____7767 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7767
                                   else ());
                                  (let uu____7769 =
                                     solve_t env eq_prob
                                       (let uu___158_7770 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7770.wl_deferred);
                                          ctr = (uu___158_7770.ctr);
                                          defer_ok = (uu___158_7770.defer_ok);
                                          smt_ok = (uu___158_7770.smt_ok);
                                          tcenv = (uu___158_7770.tcenv)
                                        }) in
                                   match uu____7769 with
                                   | Success uu____7772 ->
                                       let wl1 =
                                         let uu___159_7774 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7774.wl_deferred);
                                           ctr = (uu___159_7774.ctr);
                                           defer_ok =
                                             (uu___159_7774.defer_ok);
                                           smt_ok = (uu___159_7774.smt_ok);
                                           tcenv = (uu___159_7774.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7776 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7779 -> None))))
                   | uu____7780 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7845 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7845
                      then
                        let uu____7846 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7846
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7878 = hd1 in
                      let uu____7879 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7878.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7878.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7879
                      } in
                    let hd21 =
                      let uu___161_7883 = hd2 in
                      let uu____7884 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7883.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7883.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7884
                      } in
                    let prob =
                      let uu____7888 =
                        let uu____7891 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7891 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7888 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7899 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7899 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7902 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7902 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7920 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7923 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7920 uu____7923 in
                         ((let uu____7929 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7929
                           then
                             let uu____7930 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7931 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7930 uu____7931
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7946 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7952 = aux scope env [] bs1 bs2 in
              match uu____7952 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7968 = compress_tprob wl problem in
        solve_t' env uu____7968 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____8001 = head_matches_delta env1 wl1 t1 t2 in
          match uu____8001 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8018,uu____8019) ->
                   let may_relate head3 =
                     let uu____8034 =
                       let uu____8035 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8035.FStar_Syntax_Syntax.n in
                     match uu____8034 with
                     | FStar_Syntax_Syntax.Tm_name uu____8038 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8039 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8056 -> false in
                   let uu____8057 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8057
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
                                let uu____8074 =
                                  let uu____8075 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8075 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8074 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8077 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8077
                   else giveup env1 "head mismatch" orig
               | (uu____8079,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8087 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8087.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8087.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8087.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8087.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8087.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8087.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8087.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8087.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8088,None ) ->
                   ((let uu____8095 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8095
                     then
                       let uu____8096 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8097 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8098 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8099 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8096
                         uu____8097 uu____8098 uu____8099
                     else ());
                    (let uu____8101 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8101 with
                     | (head11,args1) ->
                         let uu____8127 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8127 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8167 =
                                  let uu____8168 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8169 = args_to_string args1 in
                                  let uu____8170 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8171 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8168 uu____8169 uu____8170
                                    uu____8171 in
                                giveup env1 uu____8167 orig
                              else
                                (let uu____8173 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8176 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8176 = FStar_Syntax_Util.Equal) in
                                 if uu____8173
                                 then
                                   let uu____8177 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8177 with
                                   | USolved wl2 ->
                                       let uu____8179 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8179
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8183 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8183 with
                                    | (base1,refinement1) ->
                                        let uu____8209 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8209 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8263 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8263 with
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
                                                           (fun uu____8273 
                                                              ->
                                                              fun uu____8274 
                                                                ->
                                                                match 
                                                                  (uu____8273,
                                                                    uu____8274)
                                                                with
                                                                | ((a,uu____8284),
                                                                   (a',uu____8286))
                                                                    ->
                                                                    let uu____8291
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
                                                                    uu____8291)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8297 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8297 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8301 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_8334 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8334.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8354 = p in
          match uu____8354 with
          | (((u,k),xs,c),ps,(h,uu____8365,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8414 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8414 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8428 = h gs_xs in
                     let uu____8429 =
                       let uu____8436 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8436
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8428 uu____8429 in
                   ((let uu____8467 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8467
                     then
                       let uu____8468 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8469 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8470 = FStar_Syntax_Print.term_to_string im in
                       let uu____8471 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8472 =
                         let uu____8473 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8473
                           (FStar_String.concat ", ") in
                       let uu____8476 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8468 uu____8469 uu____8470 uu____8471
                         uu____8472 uu____8476
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_8494 =
          match uu___129_8494 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8523 = p in
          match uu____8523 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8581 = FStar_List.nth ps i in
              (match uu____8581 with
               | (pi,uu____8584) ->
                   let uu____8589 = FStar_List.nth xs i in
                   (match uu____8589 with
                    | (xi,uu____8596) ->
                        let rec gs k =
                          let uu____8605 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8605 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8657)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8665 = new_uvar r xs k_a in
                                    (match uu____8665 with
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
                                         let uu____8684 = aux subst2 tl1 in
                                         (match uu____8684 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8699 =
                                                let uu____8701 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8701 :: gi_xs' in
                                              let uu____8702 =
                                                let uu____8704 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8704 :: gi_ps' in
                                              (uu____8699, uu____8702))) in
                              aux [] bs in
                        let uu____8707 =
                          let uu____8708 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8708 in
                        if uu____8707
                        then None
                        else
                          (let uu____8711 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8711 with
                           | (g_xs,uu____8718) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8725 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8730 =
                                   let uu____8737 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8737
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8725
                                   uu____8730 in
                               let sub1 =
                                 let uu____8768 =
                                   let uu____8771 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8778 =
                                     let uu____8781 =
                                       FStar_List.map
                                         (fun uu____8787  ->
                                            match uu____8787 with
                                            | (uu____8792,uu____8793,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8781 in
                                   mk_problem (p_scope orig) orig uu____8771
                                     (p_rel orig) uu____8778 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8768 in
                               ((let uu____8803 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8803
                                 then
                                   let uu____8804 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8805 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8804 uu____8805
                                 else ());
                                (let wl2 =
                                   let uu____8808 =
                                     let uu____8810 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8810 in
                                   solve_prob orig uu____8808
                                     [TERM (u, proj)] wl1 in
                                 let uu____8815 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8815))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8839 = lhs in
          match uu____8839 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8862 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8862 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8884 =
                        let uu____8910 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8910) in
                      Some uu____8884
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8993 =
                           let uu____8997 =
                             let uu____8998 = FStar_Syntax_Subst.compress k in
                             uu____8998.FStar_Syntax_Syntax.n in
                           (uu____8997, args) in
                         match uu____8993 with
                         | (uu____9005,[]) ->
                             let uu____9007 =
                               let uu____9013 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9013) in
                             Some uu____9007
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9024,uu____9025) ->
                             let uu____9038 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9038 with
                              | (uv1,uv_args) ->
                                  let uu____9067 =
                                    let uu____9068 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9068.FStar_Syntax_Syntax.n in
                                  (match uu____9067 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9075) ->
                                       let uu____9092 =
                                         pat_vars env [] uv_args in
                                       (match uu____9092 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9106  ->
                                                      let uu____9107 =
                                                        let uu____9108 =
                                                          let uu____9109 =
                                                            let uu____9112 =
                                                              let uu____9113
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9113
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9112 in
                                                          fst uu____9109 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9108 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9107)) in
                                            let c1 =
                                              let uu____9119 =
                                                let uu____9120 =
                                                  let uu____9123 =
                                                    let uu____9124 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9124
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9123 in
                                                fst uu____9120 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9119 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9133 =
                                                let uu____9140 =
                                                  let uu____9146 =
                                                    let uu____9147 =
                                                      let uu____9150 =
                                                        let uu____9151 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9151
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9150 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9147 in
                                                  FStar_Util.Inl uu____9146 in
                                                Some uu____9140 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9133 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9171 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9174,uu____9175)
                             ->
                             let uu____9187 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9187 with
                              | (uv1,uv_args) ->
                                  let uu____9216 =
                                    let uu____9217 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9217.FStar_Syntax_Syntax.n in
                                  (match uu____9216 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9224) ->
                                       let uu____9241 =
                                         pat_vars env [] uv_args in
                                       (match uu____9241 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9255  ->
                                                      let uu____9256 =
                                                        let uu____9257 =
                                                          let uu____9258 =
                                                            let uu____9261 =
                                                              let uu____9262
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9262
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9261 in
                                                          fst uu____9258 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9257 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9256)) in
                                            let c1 =
                                              let uu____9268 =
                                                let uu____9269 =
                                                  let uu____9272 =
                                                    let uu____9273 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9273
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9272 in
                                                fst uu____9269 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9268 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9282 =
                                                let uu____9289 =
                                                  let uu____9295 =
                                                    let uu____9296 =
                                                      let uu____9299 =
                                                        let uu____9300 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9300
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9299 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9296 in
                                                  FStar_Util.Inl uu____9295 in
                                                Some uu____9289 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9282 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9320 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9325)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9351 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9351
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9370 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9370 with
                                  | (args1,rest) ->
                                      let uu____9386 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9386 with
                                       | (xs2,c2) ->
                                           let uu____9394 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9394
                                             (fun uu____9405  ->
                                                match uu____9405 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9427 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9427 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9473 =
                                        let uu____9476 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9476 in
                                      FStar_All.pipe_right uu____9473
                                        (fun _0_57  -> Some _0_57))
                         | uu____9484 ->
                             let uu____9488 =
                               let uu____9489 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9490 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9491 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9489 uu____9490 uu____9491 in
                             failwith uu____9488 in
                       let uu____9495 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9495
                         (fun uu____9523  ->
                            match uu____9523 with
                            | (xs1,c1) ->
                                let uu____9551 =
                                  let uu____9574 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9574) in
                                Some uu____9551)) in
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
                     let uu____9646 = imitate orig env wl1 st in
                     match uu____9646 with
                     | Failed uu____9651 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9657 = project orig env wl1 i st in
                      match uu____9657 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9664) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9678 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9678 with
                | (hd1,uu____9689) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9704 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9712 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9713 -> true
                     | uu____9728 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9731 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9731
                         then true
                         else
                           ((let uu____9734 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9734
                             then
                               let uu____9735 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9735
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9743 =
                    let uu____9746 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9746 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9743 FStar_Syntax_Free.names in
                let uu____9777 = FStar_Util.set_is_empty fvs_hd in
                if uu____9777
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9786 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9786 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9794 =
                            let uu____9795 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9795 in
                          giveup_or_defer1 orig uu____9794
                        else
                          (let uu____9797 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9797
                           then
                             let uu____9798 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9798
                              then
                                let uu____9799 = subterms args_lhs in
                                imitate' orig env wl1 uu____9799
                              else
                                ((let uu____9803 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9803
                                  then
                                    let uu____9804 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9805 = names_to_string fvs1 in
                                    let uu____9806 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9804 uu____9805 uu____9806
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9811 ->
                                        let uu____9812 = sn_binders env vars in
                                        u_abs k_uv uu____9812 t21 in
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
                               (let uu____9821 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9821
                                then
                                  ((let uu____9823 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9823
                                    then
                                      let uu____9824 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9825 = names_to_string fvs1 in
                                      let uu____9826 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9824 uu____9825 uu____9826
                                    else ());
                                   (let uu____9828 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9828
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
                     (let uu____9839 =
                        let uu____9840 = FStar_Syntax_Free.names t1 in
                        check_head uu____9840 t2 in
                      if uu____9839
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9844 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9844
                          then
                            let uu____9845 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9845
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9848 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9848 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9890 =
               match uu____9890 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____9921 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____9921 with
                    | (all_formals,uu____9932) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10024  ->
                                        match uu____10024 with
                                        | (x,imp) ->
                                            let uu____10031 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10031, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10039 = FStar_Syntax_Util.type_u () in
                                match uu____10039 with
                                | (t1,uu____10043) ->
                                    let uu____10044 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10044 in
                              let uu____10047 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10047 with
                               | (t',tm_u1) ->
                                   let uu____10054 = destruct_flex_t t' in
                                   (match uu____10054 with
                                    | (uu____10076,u1,k11,uu____10079) ->
                                        let sol =
                                          let uu____10111 =
                                            let uu____10116 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10116) in
                                          TERM uu____10111 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10180 = pat_var_opt env pat_args hd1 in
                              (match uu____10180 with
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
                                              (fun uu____10209  ->
                                                 match uu____10209 with
                                                 | (x,uu____10213) ->
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
                                      let uu____10219 =
                                        let uu____10220 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10220 in
                                      if uu____10219
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10224 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10224 formals1
                                           tl1)))
                          | uu____10230 -> failwith "Impossible" in
                        let uu____10241 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10241 all_formals args) in
             let solve_both_pats wl1 uu____10281 uu____10282 r =
               match (uu____10281, uu____10282) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10396 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10396
                   then
                     let uu____10397 = solve_prob orig None [] wl1 in
                     solve env uu____10397
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10412 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10412
                       then
                         let uu____10413 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10414 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10415 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10416 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10417 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10413 uu____10414 uu____10415 uu____10416
                           uu____10417
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10459 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10459 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10467 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10467 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10497 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10497 in
                                  let uu____10500 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10500 k3)
                           else
                             (let uu____10503 =
                                let uu____10504 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10505 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10506 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10504 uu____10505 uu____10506 in
                              failwith uu____10503) in
                       let uu____10507 =
                         let uu____10513 =
                           let uu____10521 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10521 in
                         match uu____10513 with
                         | (bs,k1') ->
                             let uu____10539 =
                               let uu____10547 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10547 in
                             (match uu____10539 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10568 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10568 in
                                  let uu____10573 =
                                    let uu____10576 =
                                      let uu____10577 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10577.FStar_Syntax_Syntax.n in
                                    let uu____10580 =
                                      let uu____10581 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10581.FStar_Syntax_Syntax.n in
                                    (uu____10576, uu____10580) in
                                  (match uu____10573 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10589,uu____10590) ->
                                       (k1', [sub_prob])
                                   | (uu____10594,FStar_Syntax_Syntax.Tm_type
                                      uu____10595) -> (k2', [sub_prob])
                                   | uu____10599 ->
                                       let uu____10602 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10602 with
                                        | (t,uu____10611) ->
                                            let uu____10612 = new_uvar r zs t in
                                            (match uu____10612 with
                                             | (k_zs,uu____10621) ->
                                                 let kprob =
                                                   let uu____10623 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10623 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10507 with
                       | (k_u',sub_probs) ->
                           let uu____10637 =
                             let uu____10645 =
                               let uu____10646 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10646 in
                             let uu____10651 =
                               let uu____10654 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10654 in
                             let uu____10657 =
                               let uu____10660 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10660 in
                             (uu____10645, uu____10651, uu____10657) in
                           (match uu____10637 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10679 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10679 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10691 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10691
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10695 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10695 with
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
             let solve_one_pat uu____10727 uu____10728 =
               match (uu____10727, uu____10728) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10792 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10792
                     then
                       let uu____10793 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10794 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10793 uu____10794
                     else ());
                    (let uu____10796 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____10796
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10803  ->
                              fun uu____10804  ->
                                match (uu____10803, uu____10804) with
                                | ((a,uu____10814),(t21,uu____10816)) ->
                                    let uu____10821 =
                                      let uu____10824 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10824
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10821
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10828 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10828 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10838 = occurs_check env wl (u1, k1) t21 in
                        match uu____10838 with
                        | (occurs_ok,uu____10843) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10848 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10848
                            then
                              let sol =
                                let uu____10850 =
                                  let uu____10855 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10855) in
                                TERM uu____10850 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10860 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10860
                               then
                                 let uu____10861 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10861 with
                                 | (sol,(uu____10871,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10881 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10881
                                       then
                                         let uu____10882 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10882
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10887 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10889 = lhs in
             match uu____10889 with
             | (t1,u1,k1,args1) ->
                 let uu____10894 = rhs in
                 (match uu____10894 with
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
                       | uu____10920 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10926 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10926 with
                              | (sol,uu____10933) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10936 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10936
                                    then
                                      let uu____10937 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10937
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10942 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10944 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10944
        then
          let uu____10945 = solve_prob orig None [] wl in
          solve env uu____10945
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10949 = FStar_Util.physical_equality t1 t2 in
           if uu____10949
           then
             let uu____10950 = solve_prob orig None [] wl in
             solve env uu____10950
           else
             ((let uu____10953 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10953
               then
                 let uu____10954 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10954
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10957,uu____10958) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10959,FStar_Syntax_Syntax.Tm_bvar uu____10960) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_11000 =
                     match uu___130_11000 with
                     | [] -> c
                     | bs ->
                         let uu____11014 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11014 in
                   let uu____11024 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11024 with
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
                                   let uu____11110 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11110
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11112 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11112))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11189 =
                     match uu___131_11189 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11224 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11224 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11307 =
                                   let uu____11310 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11311 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11310
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11311 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11307))
               | (FStar_Syntax_Syntax.Tm_abs uu____11314,uu____11315) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11338 -> true
                     | uu____11353 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11381 =
                     let uu____11392 = maybe_eta t1 in
                     let uu____11397 = maybe_eta t2 in
                     (uu____11392, uu____11397) in
                   (match uu____11381 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11428 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11428.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11428.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11428.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11428.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11428.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11428.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11428.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11428.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11447 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11447
                        then
                          let uu____11448 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11448 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11469 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11469
                        then
                          let uu____11470 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11470 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11475 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11486,FStar_Syntax_Syntax.Tm_abs uu____11487) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11510 -> true
                     | uu____11525 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11553 =
                     let uu____11564 = maybe_eta t1 in
                     let uu____11569 = maybe_eta t2 in
                     (uu____11564, uu____11569) in
                   (match uu____11553 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11600 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11600.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11600.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11600.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11600.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11600.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11600.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11600.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11600.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11619 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11619
                        then
                          let uu____11620 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11620 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11641 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11641
                        then
                          let uu____11642 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11642 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11647 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11658,FStar_Syntax_Syntax.Tm_refine uu____11659) ->
                   let uu____11668 = as_refinement env wl t1 in
                   (match uu____11668 with
                    | (x1,phi1) ->
                        let uu____11673 = as_refinement env wl t2 in
                        (match uu____11673 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11679 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11679 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11712 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11712
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11716 =
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
                                 let uu____11722 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11722 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11729 =
                                   let uu____11732 =
                                     let uu____11733 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11733 :: (p_scope orig) in
                                   mk_problem uu____11732 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11729 in
                               let uu____11736 =
                                 solve env1
                                   (let uu___165_11737 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_11737.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_11737.smt_ok);
                                      tcenv = (uu___165_11737.tcenv)
                                    }) in
                               (match uu____11736 with
                                | Failed uu____11741 -> fallback ()
                                | Success uu____11744 ->
                                    let guard =
                                      let uu____11748 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____11751 =
                                        let uu____11752 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____11752
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11748
                                        uu____11751 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___166_11759 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_11759.attempting);
                                        wl_deferred =
                                          (uu___166_11759.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_11759.defer_ok);
                                        smt_ok = (uu___166_11759.smt_ok);
                                        tcenv = (uu___166_11759.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11761,FStar_Syntax_Syntax.Tm_uvar uu____11762) ->
                   let uu____11783 = destruct_flex_t t1 in
                   let uu____11784 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11783 uu____11784
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11785;
                     FStar_Syntax_Syntax.tk = uu____11786;
                     FStar_Syntax_Syntax.pos = uu____11787;
                     FStar_Syntax_Syntax.vars = uu____11788;_},uu____11789),FStar_Syntax_Syntax.Tm_uvar
                  uu____11790) ->
                   let uu____11825 = destruct_flex_t t1 in
                   let uu____11826 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11825 uu____11826
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11827,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11828;
                     FStar_Syntax_Syntax.tk = uu____11829;
                     FStar_Syntax_Syntax.pos = uu____11830;
                     FStar_Syntax_Syntax.vars = uu____11831;_},uu____11832))
                   ->
                   let uu____11867 = destruct_flex_t t1 in
                   let uu____11868 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11867 uu____11868
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11869;
                     FStar_Syntax_Syntax.tk = uu____11870;
                     FStar_Syntax_Syntax.pos = uu____11871;
                     FStar_Syntax_Syntax.vars = uu____11872;_},uu____11873),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11874;
                     FStar_Syntax_Syntax.tk = uu____11875;
                     FStar_Syntax_Syntax.pos = uu____11876;
                     FStar_Syntax_Syntax.vars = uu____11877;_},uu____11878))
                   ->
                   let uu____11927 = destruct_flex_t t1 in
                   let uu____11928 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11927 uu____11928
               | (FStar_Syntax_Syntax.Tm_uvar uu____11929,uu____11930) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11941 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11941 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11945;
                     FStar_Syntax_Syntax.tk = uu____11946;
                     FStar_Syntax_Syntax.pos = uu____11947;
                     FStar_Syntax_Syntax.vars = uu____11948;_},uu____11949),uu____11950)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11975 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____11975 t2 wl
               | (uu____11979,FStar_Syntax_Syntax.Tm_uvar uu____11980) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11991,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11992;
                     FStar_Syntax_Syntax.tk = uu____11993;
                     FStar_Syntax_Syntax.pos = uu____11994;
                     FStar_Syntax_Syntax.vars = uu____11995;_},uu____11996))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12021,FStar_Syntax_Syntax.Tm_type uu____12022) ->
                   solve_t' env
                     (let uu___167_12033 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12033.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12033.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12033.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12033.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12033.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12033.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12033.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12033.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12033.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12034;
                     FStar_Syntax_Syntax.tk = uu____12035;
                     FStar_Syntax_Syntax.pos = uu____12036;
                     FStar_Syntax_Syntax.vars = uu____12037;_},uu____12038),FStar_Syntax_Syntax.Tm_type
                  uu____12039) ->
                   solve_t' env
                     (let uu___167_12064 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12064.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12064.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12064.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12064.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12064.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12064.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12064.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12064.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12064.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12065,FStar_Syntax_Syntax.Tm_arrow uu____12066) ->
                   solve_t' env
                     (let uu___167_12084 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12084.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12084.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12084.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12084.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12084.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12084.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12084.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12084.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12084.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12085;
                     FStar_Syntax_Syntax.tk = uu____12086;
                     FStar_Syntax_Syntax.pos = uu____12087;
                     FStar_Syntax_Syntax.vars = uu____12088;_},uu____12089),FStar_Syntax_Syntax.Tm_arrow
                  uu____12090) ->
                   solve_t' env
                     (let uu___167_12122 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12122.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12122.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12122.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12122.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12122.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12122.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12122.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12122.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12122.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12123,uu____12124) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12137 =
                        let uu____12138 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12138 in
                      if uu____12137
                      then
                        let uu____12139 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_12142 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12142.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12142.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12142.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12142.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12142.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12142.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12142.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12142.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12142.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12143 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12139 uu____12143 t2
                          wl
                      else
                        (let uu____12148 = base_and_refinement env wl t2 in
                         match uu____12148 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12178 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_12181 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12181.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12181.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12181.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12181.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12181.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12181.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12181.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12181.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12181.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12182 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12178
                                    uu____12182 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12197 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12197.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12197.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12200 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12200 in
                                  let guard =
                                    let uu____12208 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12208
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12214;
                     FStar_Syntax_Syntax.tk = uu____12215;
                     FStar_Syntax_Syntax.pos = uu____12216;
                     FStar_Syntax_Syntax.vars = uu____12217;_},uu____12218),uu____12219)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12246 =
                        let uu____12247 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12247 in
                      if uu____12246
                      then
                        let uu____12248 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_12251 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12251.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12251.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12251.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12251.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12251.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12251.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12251.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12251.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12251.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12252 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12248 uu____12252 t2
                          wl
                      else
                        (let uu____12257 = base_and_refinement env wl t2 in
                         match uu____12257 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12287 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_12290 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12290.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12290.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12290.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12290.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12290.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12290.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12290.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12290.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12290.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12291 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12287
                                    uu____12291 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12306 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12306.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12306.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12309 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12309 in
                                  let guard =
                                    let uu____12317 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12317
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12323,FStar_Syntax_Syntax.Tm_uvar uu____12324) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12336 = base_and_refinement env wl t1 in
                      match uu____12336 with
                      | (t_base,uu____12347) ->
                          solve_t env
                            (let uu___171_12362 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12362.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12362.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12362.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12362.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12362.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12362.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12362.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12362.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12365,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12366;
                     FStar_Syntax_Syntax.tk = uu____12367;
                     FStar_Syntax_Syntax.pos = uu____12368;
                     FStar_Syntax_Syntax.vars = uu____12369;_},uu____12370))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12396 = base_and_refinement env wl t1 in
                      match uu____12396 with
                      | (t_base,uu____12407) ->
                          solve_t env
                            (let uu___171_12422 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12422.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12422.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12422.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12422.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12422.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12422.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12422.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12422.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12425,uu____12426) ->
                   let t21 =
                     let uu____12434 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12434 in
                   solve_t env
                     (let uu___172_12447 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_12447.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_12447.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_12447.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_12447.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_12447.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_12447.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_12447.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_12447.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_12447.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12448,FStar_Syntax_Syntax.Tm_refine uu____12449) ->
                   let t11 =
                     let uu____12457 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12457 in
                   solve_t env
                     (let uu___173_12470 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12470.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12470.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_12470.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_12470.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12470.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12470.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12470.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12470.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12470.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12473,uu____12474) ->
                   let head1 =
                     let uu____12493 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12493 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12524 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12524 FStar_Pervasives.fst in
                   let uu____12552 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12552
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12561 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12561
                      then
                        let guard =
                          let uu____12568 =
                            let uu____12569 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12569 = FStar_Syntax_Util.Equal in
                          if uu____12568
                          then None
                          else
                            (let uu____12572 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12572) in
                        let uu____12574 = solve_prob orig guard [] wl in
                        solve env uu____12574
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12577,uu____12578) ->
                   let head1 =
                     let uu____12586 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12586 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12617 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12617 FStar_Pervasives.fst in
                   let uu____12645 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12645
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12654 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12654
                      then
                        let guard =
                          let uu____12661 =
                            let uu____12662 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12662 = FStar_Syntax_Util.Equal in
                          if uu____12661
                          then None
                          else
                            (let uu____12665 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12665) in
                        let uu____12667 = solve_prob orig guard [] wl in
                        solve env uu____12667
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12670,uu____12671) ->
                   let head1 =
                     let uu____12675 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12675 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12706 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12706 FStar_Pervasives.fst in
                   let uu____12734 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12734
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12743 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12743
                      then
                        let guard =
                          let uu____12750 =
                            let uu____12751 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12751 = FStar_Syntax_Util.Equal in
                          if uu____12750
                          then None
                          else
                            (let uu____12754 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12754) in
                        let uu____12756 = solve_prob orig guard [] wl in
                        solve env uu____12756
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12759,uu____12760) ->
                   let head1 =
                     let uu____12764 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12764 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12795 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12795 FStar_Pervasives.fst in
                   let uu____12823 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12823
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12832 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12832
                      then
                        let guard =
                          let uu____12839 =
                            let uu____12840 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12840 = FStar_Syntax_Util.Equal in
                          if uu____12839
                          then None
                          else
                            (let uu____12843 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12843) in
                        let uu____12845 = solve_prob orig guard [] wl in
                        solve env uu____12845
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12848,uu____12849) ->
                   let head1 =
                     let uu____12853 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12853 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12884 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12884 FStar_Pervasives.fst in
                   let uu____12912 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12912
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12921 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12921
                      then
                        let guard =
                          let uu____12928 =
                            let uu____12929 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12929 = FStar_Syntax_Util.Equal in
                          if uu____12928
                          then None
                          else
                            (let uu____12932 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____12932) in
                        let uu____12934 = solve_prob orig guard [] wl in
                        solve env uu____12934
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12937,uu____12938) ->
                   let head1 =
                     let uu____12951 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12951 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12982 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12982 FStar_Pervasives.fst in
                   let uu____13010 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13010
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13019 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13019
                      then
                        let guard =
                          let uu____13026 =
                            let uu____13027 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13027 = FStar_Syntax_Util.Equal in
                          if uu____13026
                          then None
                          else
                            (let uu____13030 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____13030) in
                        let uu____13032 = solve_prob orig guard [] wl in
                        solve env uu____13032
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13035,FStar_Syntax_Syntax.Tm_match uu____13036) ->
                   let head1 =
                     let uu____13055 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13055 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13086 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13086 FStar_Pervasives.fst in
                   let uu____13114 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13114
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13123 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13123
                      then
                        let guard =
                          let uu____13130 =
                            let uu____13131 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13131 = FStar_Syntax_Util.Equal in
                          if uu____13130
                          then None
                          else
                            (let uu____13134 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____13134) in
                        let uu____13136 = solve_prob orig guard [] wl in
                        solve env uu____13136
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13139,FStar_Syntax_Syntax.Tm_uinst uu____13140) ->
                   let head1 =
                     let uu____13148 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13148 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13179 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13179 FStar_Pervasives.fst in
                   let uu____13207 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13207
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13216 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13216
                      then
                        let guard =
                          let uu____13223 =
                            let uu____13224 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13224 = FStar_Syntax_Util.Equal in
                          if uu____13223
                          then None
                          else
                            (let uu____13227 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13227) in
                        let uu____13229 = solve_prob orig guard [] wl in
                        solve env uu____13229
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13232,FStar_Syntax_Syntax.Tm_name uu____13233) ->
                   let head1 =
                     let uu____13237 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13237 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13268 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13268 FStar_Pervasives.fst in
                   let uu____13296 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13296
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13305 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13305
                      then
                        let guard =
                          let uu____13312 =
                            let uu____13313 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13313 = FStar_Syntax_Util.Equal in
                          if uu____13312
                          then None
                          else
                            (let uu____13316 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13316) in
                        let uu____13318 = solve_prob orig guard [] wl in
                        solve env uu____13318
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13321,FStar_Syntax_Syntax.Tm_constant uu____13322) ->
                   let head1 =
                     let uu____13326 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13326 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13357 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13357 FStar_Pervasives.fst in
                   let uu____13385 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13385
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13394 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13394
                      then
                        let guard =
                          let uu____13401 =
                            let uu____13402 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13402 = FStar_Syntax_Util.Equal in
                          if uu____13401
                          then None
                          else
                            (let uu____13405 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13405) in
                        let uu____13407 = solve_prob orig guard [] wl in
                        solve env uu____13407
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13410,FStar_Syntax_Syntax.Tm_fvar uu____13411) ->
                   let head1 =
                     let uu____13415 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13415 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13446 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13446 FStar_Pervasives.fst in
                   let uu____13474 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13474
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13483 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13483
                      then
                        let guard =
                          let uu____13490 =
                            let uu____13491 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13491 = FStar_Syntax_Util.Equal in
                          if uu____13490
                          then None
                          else
                            (let uu____13494 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13494) in
                        let uu____13496 = solve_prob orig guard [] wl in
                        solve env uu____13496
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13499,FStar_Syntax_Syntax.Tm_app uu____13500) ->
                   let head1 =
                     let uu____13513 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13513 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13544 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13544 FStar_Pervasives.fst in
                   let uu____13572 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13572
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13581 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13581
                      then
                        let guard =
                          let uu____13588 =
                            let uu____13589 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13589 = FStar_Syntax_Util.Equal in
                          if uu____13588
                          then None
                          else
                            (let uu____13592 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13592) in
                        let uu____13594 = solve_prob orig guard [] wl in
                        solve env uu____13594
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13598,uu____13599),uu____13600) ->
                   solve_t' env
                     (let uu___174_13629 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_13629.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_13629.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_13629.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_13629.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_13629.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_13629.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_13629.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_13629.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_13629.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13632,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13634,uu____13635)) ->
                   solve_t' env
                     (let uu___175_13664 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13664.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_13664.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13664.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_13664.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13664.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13664.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13664.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13664.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13664.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13665,uu____13666) ->
                   let uu____13674 =
                     let uu____13675 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13676 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13675
                       uu____13676 in
                   failwith uu____13674
               | (FStar_Syntax_Syntax.Tm_meta uu____13677,uu____13678) ->
                   let uu____13683 =
                     let uu____13684 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13685 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13684
                       uu____13685 in
                   failwith uu____13683
               | (FStar_Syntax_Syntax.Tm_delayed uu____13686,uu____13687) ->
                   let uu____13708 =
                     let uu____13709 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13710 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13709
                       uu____13710 in
                   failwith uu____13708
               | (uu____13711,FStar_Syntax_Syntax.Tm_meta uu____13712) ->
                   let uu____13717 =
                     let uu____13718 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13719 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13718
                       uu____13719 in
                   failwith uu____13717
               | (uu____13720,FStar_Syntax_Syntax.Tm_delayed uu____13721) ->
                   let uu____13742 =
                     let uu____13743 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13744 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13743
                       uu____13744 in
                   failwith uu____13742
               | (uu____13745,FStar_Syntax_Syntax.Tm_let uu____13746) ->
                   let uu____13754 =
                     let uu____13755 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13756 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13755
                       uu____13756 in
                   failwith uu____13754
               | uu____13757 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13789 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13789
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13797  ->
                  fun uu____13798  ->
                    match (uu____13797, uu____13798) with
                    | ((a1,uu____13808),(a2,uu____13810)) ->
                        let uu____13815 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13815)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13821 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13821 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13841 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13848)::[] -> wp1
              | uu____13861 ->
                  let uu____13867 =
                    let uu____13868 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13868 in
                  failwith uu____13867 in
            let uu____13871 =
              let uu____13877 =
                let uu____13878 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13878 in
              [uu____13877] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13871;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13879 = lift_c1 () in solve_eq uu____13879 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13883  ->
                       match uu___132_13883 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13884 -> false)) in
             let uu____13885 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13909)::uu____13910,(wp2,uu____13912)::uu____13913)
                   -> (wp1, wp2)
               | uu____13954 ->
                   let uu____13967 =
                     let uu____13968 =
                       let uu____13971 =
                         let uu____13972 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____13973 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13972 uu____13973 in
                       (uu____13971, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____13968 in
                   raise uu____13967 in
             match uu____13885 with
             | (wpc1,wpc2) ->
                 let uu____13990 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____13990
                 then
                   let uu____13993 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____13993 wl
                 else
                   (let uu____13997 =
                      let uu____14001 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14001 in
                    match uu____13997 with
                    | (c2_decl,qualifiers) ->
                        let uu____14013 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14013
                        then
                          let c1_repr =
                            let uu____14016 =
                              let uu____14017 =
                                let uu____14018 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14018 in
                              let uu____14019 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14017 uu____14019 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14016 in
                          let c2_repr =
                            let uu____14021 =
                              let uu____14022 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14023 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14022 uu____14023 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14021 in
                          let prob =
                            let uu____14025 =
                              let uu____14028 =
                                let uu____14029 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14030 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14029
                                  uu____14030 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14028 in
                            FStar_TypeChecker_Common.TProb uu____14025 in
                          let wl1 =
                            let uu____14032 =
                              let uu____14034 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14034 in
                            solve_prob orig uu____14032 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14041 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14041
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14043 =
                                     let uu____14046 =
                                       let uu____14047 =
                                         let uu____14057 =
                                           let uu____14058 =
                                             let uu____14059 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14059] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14058 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14060 =
                                           let uu____14062 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14063 =
                                             let uu____14065 =
                                               let uu____14066 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14066 in
                                             [uu____14065] in
                                           uu____14062 :: uu____14063 in
                                         (uu____14057, uu____14060) in
                                       FStar_Syntax_Syntax.Tm_app uu____14047 in
                                     FStar_Syntax_Syntax.mk uu____14046 in
                                   uu____14043
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14077 =
                                    let uu____14080 =
                                      let uu____14081 =
                                        let uu____14091 =
                                          let uu____14092 =
                                            let uu____14093 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14093] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14092 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14094 =
                                          let uu____14096 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14097 =
                                            let uu____14099 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14100 =
                                              let uu____14102 =
                                                let uu____14103 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14103 in
                                              [uu____14102] in
                                            uu____14099 :: uu____14100 in
                                          uu____14096 :: uu____14097 in
                                        (uu____14091, uu____14094) in
                                      FStar_Syntax_Syntax.Tm_app uu____14081 in
                                    FStar_Syntax_Syntax.mk uu____14080 in
                                  uu____14077
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14114 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14114 in
                           let wl1 =
                             let uu____14120 =
                               let uu____14122 =
                                 let uu____14125 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14125 g in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____14122 in
                             solve_prob orig uu____14120 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14135 = FStar_Util.physical_equality c1 c2 in
        if uu____14135
        then
          let uu____14136 = solve_prob orig None [] wl in
          solve env uu____14136
        else
          ((let uu____14139 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14139
            then
              let uu____14140 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14141 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14140
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14141
            else ());
           (let uu____14143 =
              let uu____14146 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14147 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14146, uu____14147) in
            match uu____14143 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14151),FStar_Syntax_Syntax.Total
                    (t2,uu____14153)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14166 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14166 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14169,FStar_Syntax_Syntax.Total uu____14170) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14182),FStar_Syntax_Syntax.Total
                    (t2,uu____14184)) ->
                     let uu____14197 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14197 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14201),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14203)) ->
                     let uu____14216 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14216 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14220),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14222)) ->
                     let uu____14235 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14235 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14238,FStar_Syntax_Syntax.Comp uu____14239) ->
                     let uu____14245 =
                       let uu___176_14248 = problem in
                       let uu____14251 =
                         let uu____14252 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14252 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14248.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14251;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14248.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14248.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14248.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14248.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14248.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14248.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14248.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14248.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14245 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14253,FStar_Syntax_Syntax.Comp uu____14254) ->
                     let uu____14260 =
                       let uu___176_14263 = problem in
                       let uu____14266 =
                         let uu____14267 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14267 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14263.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14266;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14263.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14263.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14263.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14263.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14263.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14263.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14263.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14263.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14260 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14268,FStar_Syntax_Syntax.GTotal uu____14269) ->
                     let uu____14275 =
                       let uu___177_14278 = problem in
                       let uu____14281 =
                         let uu____14282 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14282 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14278.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14278.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14278.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14281;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14278.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14278.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14278.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14278.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14278.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14278.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14275 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14283,FStar_Syntax_Syntax.Total uu____14284) ->
                     let uu____14290 =
                       let uu___177_14293 = problem in
                       let uu____14296 =
                         let uu____14297 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14297 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14293.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14293.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14293.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14296;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14293.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14293.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14293.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14293.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14293.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14293.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14290 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14298,FStar_Syntax_Syntax.Comp uu____14299) ->
                     let uu____14300 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14300
                     then
                       let uu____14301 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14301 wl
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
                           (let uu____14311 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14311
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14313 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14313 with
                            | None  ->
                                let uu____14315 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14316 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14316) in
                                if uu____14315
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
                                  (let uu____14319 =
                                     let uu____14320 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14321 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14320 uu____14321 in
                                   giveup env uu____14319 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14326 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14342  ->
              match uu____14342 with
              | (uu____14349,uu____14350,u,uu____14352,uu____14353,uu____14354)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14326 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14372 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14372 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14382 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14394  ->
                match uu____14394 with
                | (u1,u2) ->
                    let uu____14399 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14400 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14399 uu____14400)) in
      FStar_All.pipe_right uu____14382 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14412,[])) -> "{}"
      | uu____14425 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14435 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14435
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14438 =
              FStar_List.map
                (fun uu____14442  ->
                   match uu____14442 with
                   | (uu____14445,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14438 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14449 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14449 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14487 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14487
    then
      let uu____14488 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14489 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14488
        (rel_to_string rel) uu____14489
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
            let uu____14509 =
              let uu____14511 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14511 in
            FStar_Syntax_Syntax.new_bv uu____14509 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14517 =
              let uu____14519 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14519 in
            let uu____14521 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14517 uu____14521 in
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
          let uu____14544 = FStar_Options.eager_inference () in
          if uu____14544
          then
            let uu___178_14545 = probs in
            {
              attempting = (uu___178_14545.attempting);
              wl_deferred = (uu___178_14545.wl_deferred);
              ctr = (uu___178_14545.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14545.smt_ok);
              tcenv = (uu___178_14545.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14556 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14556
              then
                let uu____14557 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14557
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
          ((let uu____14567 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14567
            then
              let uu____14568 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14568
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14572 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14572
             then
               let uu____14573 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14573
             else ());
            (let f2 =
               let uu____14576 =
                 let uu____14577 = FStar_Syntax_Util.unmeta f1 in
                 uu____14577.FStar_Syntax_Syntax.n in
               match uu____14576 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14581 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_14582 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14582.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14582.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14582.FStar_TypeChecker_Env.implicits)
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
            let uu____14597 =
              let uu____14598 =
                let uu____14599 =
                  let uu____14600 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14600
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14599;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14598 in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14597
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14633 =
        let uu____14634 =
          let uu____14635 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14635
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14634;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14633
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
          (let uu____14661 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14661
           then
             let uu____14662 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14663 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14662
               uu____14663
           else ());
          (let prob =
             let uu____14666 =
               let uu____14669 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14669 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14666 in
           let g =
             let uu____14674 =
               let uu____14676 = singleton' env prob smt_ok in
               solve_and_commit env uu____14676 (fun uu____14677  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14674 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14691 = try_teq true env t1 t2 in
        match uu____14691 with
        | None  ->
            let uu____14693 =
              let uu____14694 =
                let uu____14697 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14698 = FStar_TypeChecker_Env.get_range env in
                (uu____14697, uu____14698) in
              FStar_Errors.Error uu____14694 in
            raise uu____14693
        | Some g ->
            ((let uu____14701 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14701
              then
                let uu____14702 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14703 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14704 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14702
                  uu____14703 uu____14704
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
          (let uu____14720 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14720
           then
             let uu____14721 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14722 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14721
               uu____14722
           else ());
          (let uu____14724 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14724 with
           | (prob,x) ->
               let g =
                 let uu____14732 =
                   let uu____14734 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14734
                     (fun uu____14735  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14732 in
               ((let uu____14741 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14741
                 then
                   let uu____14742 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14743 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14744 =
                     let uu____14745 = FStar_Util.must g in
                     guard_to_string env uu____14745 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14742 uu____14743 uu____14744
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
          let uu____14769 = FStar_TypeChecker_Env.get_range env in
          let uu____14770 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____14769 uu____14770
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14782 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14782
         then
           let uu____14783 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14784 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14783
             uu____14784
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14789 =
             let uu____14792 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____14792 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14789 in
         let uu____14795 =
           let uu____14797 = singleton env prob in
           solve_and_commit env uu____14797 (fun uu____14798  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____14795)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14817  ->
        match uu____14817 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14842 =
                 let uu____14843 =
                   let uu____14846 =
                     let uu____14847 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14848 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14847 uu____14848 in
                   let uu____14849 = FStar_TypeChecker_Env.get_range env in
                   (uu____14846, uu____14849) in
                 FStar_Errors.Error uu____14843 in
               raise uu____14842) in
            let equiv1 v1 v' =
              let uu____14857 =
                let uu____14860 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14861 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14860, uu____14861) in
              match uu____14857 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14872 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14886 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14886 with
                      | FStar_Syntax_Syntax.U_unif uu____14890 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14903  ->
                                    match uu____14903 with
                                    | (u,v') ->
                                        let uu____14909 = equiv1 v1 v' in
                                        if uu____14909
                                        then
                                          let uu____14911 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____14911 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14921 -> [])) in
            let uu____14924 =
              let wl =
                let uu___180_14927 = empty_worklist env in
                {
                  attempting = (uu___180_14927.attempting);
                  wl_deferred = (uu___180_14927.wl_deferred);
                  ctr = (uu___180_14927.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_14927.smt_ok);
                  tcenv = (uu___180_14927.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14934  ->
                      match uu____14934 with
                      | (lb,v1) ->
                          let uu____14939 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____14939 with
                           | USolved wl1 -> ()
                           | uu____14941 -> fail lb v1))) in
            let rec check_ineq uu____14947 =
              match uu____14947 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14954) -> true
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
                      uu____14969,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14971,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14978) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14982,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14987 -> false) in
            let uu____14990 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14996  ->
                      match uu____14996 with
                      | (u,v1) ->
                          let uu____15001 = check_ineq (u, v1) in
                          if uu____15001
                          then true
                          else
                            ((let uu____15004 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15004
                              then
                                let uu____15005 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15006 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15005
                                  uu____15006
                              else ());
                             false))) in
            if uu____14990
            then ()
            else
              ((let uu____15010 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15010
                then
                  ((let uu____15012 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15012);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____15018 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15018))
                else ());
               (let uu____15024 =
                  let uu____15025 =
                    let uu____15028 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15028) in
                  FStar_Errors.Error uu____15025 in
                raise uu____15024))
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
      let fail uu____15061 =
        match uu____15061 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15071 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15071
       then
         let uu____15072 = wl_to_string wl in
         let uu____15073 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15072 uu____15073
       else ());
      (let g1 =
         let uu____15085 = solve_and_commit env wl fail in
         match uu____15085 with
         | Some [] ->
             let uu___181_15092 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15092.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15092.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15092.FStar_TypeChecker_Env.implicits)
             }
         | uu____15095 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15098 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15098.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15098.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15098.FStar_TypeChecker_Env.implicits)
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
            let uu___183_15124 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15124.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15124.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15124.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15125 =
            let uu____15126 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15126 in
          if uu____15125
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15132 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15132
                   then
                     let uu____15133 = FStar_TypeChecker_Env.get_range env in
                     let uu____15134 =
                       let uu____15135 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15135 in
                     FStar_Errors.diag uu____15133 uu____15134
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
                         ((let uu____15144 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15144
                           then
                             let uu____15145 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15146 =
                               let uu____15147 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15147 in
                             FStar_Errors.diag uu____15145 uu____15146
                           else ());
                          (let vcs =
                             let uu____15153 = FStar_Options.use_tactics () in
                             if uu____15153
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15167  ->
                                   match uu____15167 with
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
      let uu____15178 = discharge_guard' None env g false in
      match uu____15178 with
      | Some g1 -> g1
      | None  ->
          let uu____15183 =
            let uu____15184 =
              let uu____15187 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15187) in
            FStar_Errors.Error uu____15184 in
          raise uu____15183
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15194 = discharge_guard' None env g true in
      match uu____15194 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15206 = FStar_Syntax_Unionfind.find u in
      match uu____15206 with | None  -> true | uu____15208 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15221 = acc in
      match uu____15221 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15267 = hd1 in
               (match uu____15267 with
                | (uu____15274,env,u,tm,k,r) ->
                    let uu____15280 = unresolved u in
                    if uu____15280
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15298 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15298
                        then
                          let uu____15299 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15300 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15301 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15299 uu____15300 uu____15301
                        else ());
                       (let uu____15303 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15307 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15307.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15307.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15307.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15307.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15307.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15307.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15307.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15307.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15307.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15307.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15307.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15307.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15307.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15307.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15307.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15307.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15307.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15307.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15307.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15307.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15307.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15307.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15307.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____15303 with
                        | (uu____15308,uu____15309,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15312 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15312.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15312.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15312.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15315 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15319  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15315 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_15334 = g in
    let uu____15335 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15334.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15334.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15334.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15335
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15363 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15363 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15370 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15370
      | (reason,uu____15372,uu____15373,e,t,r)::uu____15377 ->
          let uu____15391 =
            let uu____15392 = FStar_Syntax_Print.term_to_string t in
            let uu____15393 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15392 uu____15393 in
          FStar_Errors.err r uu____15391
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15400 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15400.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15400.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15400.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15418 = try_teq false env t1 t2 in
        match uu____15418 with
        | None  -> false
        | Some g ->
            let uu____15421 = discharge_guard' None env g false in
            (match uu____15421 with
             | Some uu____15425 -> true
             | None  -> false)