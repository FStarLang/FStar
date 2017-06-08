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
    FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun x  ->
    fun g  ->
      match g with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____56;
            FStar_TypeChecker_Env.univ_ineqs = uu____57;
            FStar_TypeChecker_Env.implicits = uu____58;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
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
                  FStar_Pervasives_Native.Some uu____87 in
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
          FStar_Pervasives_Native.Some uu____74
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
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
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
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
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
            ((FStar_List.append
                (FStar_Pervasives_Native.fst
                   g1.FStar_TypeChecker_Env.univ_ineqs)
                (FStar_Pervasives_Native.fst
                   g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append
                 (FStar_Pervasives_Native.snd
                    g1.FStar_TypeChecker_Env.univ_ineqs)
                 (FStar_Pervasives_Native.snd
                    g2.FStar_TypeChecker_Env.univ_ineqs)));
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
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
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
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
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
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r in
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
                FStar_Pervasives_Native.None r in
            let uu____361 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r in
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
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____421 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____447 -> false
let __proj__UNIV__item___0:
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list;
  ctr: Prims.int;
  defer_ok: Prims.bool;
  smt_ok: Prims.bool;
  tcenv: FStar_TypeChecker_Env.env;}
type solution =
  | Success of FStar_TypeChecker_Common.deferred
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2
let uu___is_Success: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____527 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____541 -> false
let __proj__Failed__item___0:
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0
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
  fun uu___105_583  ->
    match uu___105_583 with
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
    fun uu___106_663  ->
      match uu___106_663 with
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
                            (FStar_Pervasives_Native.fst
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
    fun uu___107_701  ->
      match uu___107_701 with
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
        let uu___138_790 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___138_790.wl_deferred);
          ctr = (uu___138_790.ctr);
          defer_ok = (uu___138_790.defer_ok);
          smt_ok;
          tcenv = (uu___138_790.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___139_815 = empty_worklist env in
  let uu____816 = FStar_List.map FStar_Pervasives_Native.snd g in
  {
    attempting = uu____816;
    wl_deferred = (uu___139_815.wl_deferred);
    ctr = (uu___139_815.ctr);
    defer_ok = false;
    smt_ok = (uu___139_815.smt_ok);
    tcenv = (uu___139_815.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_828 = wl in
        {
          attempting = (uu___140_828.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_828.ctr);
          defer_ok = (uu___140_828.defer_ok);
          smt_ok = (uu___140_828.smt_ok);
          tcenv = (uu___140_828.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___141_840 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_840.wl_deferred);
        ctr = (uu___141_840.ctr);
        defer_ok = (uu___141_840.defer_ok);
        smt_ok = (uu___141_840.smt_ok);
        tcenv = (uu___141_840.tcenv)
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
  fun uu___108_856  ->
    match uu___108_856 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___142_872 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_872.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_872.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_872.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_872.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_872.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_872.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_872.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_893  ->
    match uu___109_893 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_909  ->
      match uu___110_909 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_912  ->
    match uu___111_912 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_921  ->
    match uu___112_921 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_931  ->
    match uu___113_931 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_941  ->
    match uu___114_941 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___115_952  ->
    match uu___115_952 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_963  ->
    match uu___116_963 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_972  ->
    match uu___117_972 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
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
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
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
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
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
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let guard_on_element wl problem x phi =
  match problem.FStar_TypeChecker_Common.element with
  | FStar_Pervasives_Native.None  ->
      let u =
        (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
          x.FStar_Syntax_Syntax.sort in
      FStar_Syntax_Util.mk_forall u x phi
  | FStar_Pervasives_Native.Some e ->
      FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
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
         (fun uu___118_1221  ->
            match uu___118_1221 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1228 ->
                     FStar_Unionfind.change u
                       (FStar_Pervasives_Native.Some t))
            | TERM ((u,uu____1231),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1254  ->
           match uu___119_1254 with
           | UNIV uu____1256 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1260),t) ->
               let uu____1264 = FStar_Unionfind.equivalent uv u in
               if uu____1264
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1283  ->
           match uu___120_1283 with
           | UNIV (u',t) ->
               let uu____1287 = FStar_Unionfind.equivalent u u' in
               if uu____1287
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1291 -> FStar_Pervasives_Native.None)
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
  let uu____1325 = sn env (FStar_Pervasives_Native.fst t) in
  (uu____1325, (FStar_Pervasives_Native.snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1342  ->
              match uu____1342 with
              | (x,imp) ->
                  let uu____1349 =
                    let uu___143_1350 = x in
                    let uu____1351 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1350.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1350.FStar_Syntax_Syntax.index);
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
        then
          ((x.FStar_Syntax_Syntax.sort),
            (FStar_Pervasives_Native.Some (x, phi)))
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
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____1514 =
                 let uu____1515 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1516 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1515
                   uu____1516 in
               failwith uu____1514)
    | FStar_Syntax_Syntax.Tm_uinst uu____1526 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1553 =
             let uu____1554 = FStar_Syntax_Subst.compress t1' in
             uu____1554.FStar_Syntax_Syntax.n in
           match uu____1553 with
           | FStar_Syntax_Syntax.Tm_refine uu____1566 -> aux true t1'
           | uu____1571 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1583 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1606 =
             let uu____1607 = FStar_Syntax_Subst.compress t1' in
             uu____1607.FStar_Syntax_Syntax.n in
           match uu____1606 with
           | FStar_Syntax_Syntax.Tm_refine uu____1619 -> aux true t1'
           | uu____1624 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____1636 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1668 =
             let uu____1669 = FStar_Syntax_Subst.compress t1' in
             uu____1669.FStar_Syntax_Syntax.n in
           match uu____1668 with
           | FStar_Syntax_Syntax.Tm_refine uu____1681 -> aux true t1'
           | uu____1686 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____1698 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____1710 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____1722 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1734 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1746 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____1765 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1791 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____1811 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____1830 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____1857 ->
        let uu____1862 =
          let uu____1863 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1864 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1863
            uu____1864 in
        failwith uu____1862
    | FStar_Syntax_Syntax.Tm_ascribed uu____1874 ->
        let uu____1892 =
          let uu____1893 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1894 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1893
            uu____1894 in
        failwith uu____1892
    | FStar_Syntax_Syntax.Tm_delayed uu____1904 ->
        let uu____1925 =
          let uu____1926 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1927 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1926
            uu____1927 in
        failwith uu____1925
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1937 =
          let uu____1938 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1939 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1938
            uu____1939 in
        failwith uu____1937 in
  let uu____1949 = whnf env t1 in aux false uu____1949
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1958 =
        let uu____1968 = empty_worklist env in
        base_and_refinement env uu____1968 t in
      FStar_All.pipe_right uu____1958 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____1992 = FStar_Syntax_Syntax.null_bv t in
    (uu____1992, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2012 = base_and_refinement env wl t in
  match uu____2012 with
  | (t_base,refinement) ->
      (match refinement with
       | FStar_Pervasives_Native.None  -> trivial_refinement t_base
       | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement uu____2071 =
  match uu____2071 with
  | (t_base,refopt) ->
      let uu____2085 =
        match refopt with
        | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
        | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
      (match uu____2085 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2109  ->
      match uu___121_2109 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2113 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2114 =
            let uu____2115 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2115 in
          let uu____2116 =
            let uu____2117 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2117 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2113 uu____2114
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2116
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2121 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2122 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2123 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2121 uu____2122
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2123
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2127 =
      let uu____2129 =
        let uu____2131 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2141  ->
                  match uu____2141 with | (uu____2145,uu____2146,x) -> x)) in
        FStar_List.append wl.attempting uu____2131 in
      FStar_List.map (wl_prob_to_string wl) uu____2129 in
    FStar_All.pipe_right uu____2127 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2164 =
          let uu____2174 =
            let uu____2175 = FStar_Syntax_Subst.compress k in
            uu____2175.FStar_Syntax_Syntax.n in
          match uu____2174 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2216 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2216)
              else
                (let uu____2230 = FStar_Syntax_Util.abs_formals t in
                 match uu____2230 with
                 | (ys',t1,uu____2251) ->
                     let uu____2264 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2264))
          | uu____2285 ->
              let uu____2286 =
                let uu____2292 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2292) in
              ((ys, t), uu____2286) in
        match uu____2164 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr (FStar_Parser_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2347 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2347 c in
               let uu____2349 =
                 let uu____2356 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2356
                   (fun _0_37  -> FStar_Pervasives_Native.Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2349)
let solve_prob':
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
              | FStar_Pervasives_Native.Some phi -> phi in
            let uu____2407 = p_guard prob in
            match uu____2407 with
            | (uu____2410,uv) ->
                ((let uu____2413 =
                    let uu____2414 = FStar_Syntax_Subst.compress uv in
                    uu____2414.FStar_Syntax_Syntax.n in
                  match uu____2413 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2434 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2434
                        then
                          let uu____2435 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2436 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2437 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2435
                            uu____2436 uu____2437
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2441 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2444 = wl in
                  {
                    attempting = (uu___144_2444.attempting);
                    wl_deferred = (uu___144_2444.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2444.defer_ok);
                    smt_ok = (uu___144_2444.smt_ok);
                    tcenv = (uu___144_2444.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2457 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2457
         then
           let uu____2458 = FStar_Util.string_of_int pid in
           let uu____2459 =
             let uu____2460 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2460 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2458 uu____2459
         else ());
        commit sol;
        (let uu___145_2465 = wl in
         {
           attempting = (uu___145_2465.attempting);
           wl_deferred = (uu___145_2465.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2465.defer_ok);
           smt_ok = (uu___145_2465.smt_ok);
           tcenv = (uu___145_2465.tcenv)
         })
let solve_prob:
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2494,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2502 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____2502 in
          (let uu____2508 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2508
           then
             let uu____2509 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2510 =
               let uu____2511 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2511 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2509 uu____2510
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2536 =
    let uu____2540 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2540 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2536
    (FStar_Util.for_some
       (fun uu____2561  ->
          match uu____2561 with
          | (uv,uu____2569) ->
              FStar_Unionfind.equivalent uv (FStar_Pervasives_Native.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2613 = occurs wl uk t in Prims.op_Negation uu____2613 in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____2618 =
         let uu____2619 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk) in
         let uu____2623 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2619 uu____2623 in
       FStar_Pervasives_Native.Some uu____2618) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2671 = occurs_check env wl uk t in
  match uu____2671 with
  | (occurs_ok,msg) ->
      let uu____2688 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2688, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2752 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2776  ->
            fun uu____2777  ->
              match (uu____2776, uu____2777) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2820 =
                    let uu____2821 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2821 in
                  if uu____2820
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2835 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2835
                     then
                       let uu____2842 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2842)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2752 with | (isect,uu____2864) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2913  ->
          fun uu____2914  ->
            match (uu____2913, uu____2914) with
            | ((a,uu____2924),(b,uu____2926)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2970 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2976  ->
                match uu____2976 with
                | (b,uu____2980) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2970
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____2989 -> FStar_Pervasives_Native.None
let rec pat_vars:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____3032 = pat_var_opt env seen hd1 in
            (match uu____3032 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3040 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3040
                   then
                     let uu____3041 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3041
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3053 =
      let uu____3054 = FStar_Syntax_Subst.compress t in
      uu____3054.FStar_Syntax_Syntax.n in
    match uu____3053 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3057 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3066;
           FStar_Syntax_Syntax.tk = uu____3067;
           FStar_Syntax_Syntax.pos = uu____3068;
           FStar_Syntax_Syntax.vars = uu____3069;_},uu____3070)
        -> true
    | uu____3093 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3155;
         FStar_Syntax_Syntax.pos = uu____3156;
         FStar_Syntax_Syntax.vars = uu____3157;_},args)
      -> (t, uv, k, args)
  | uu____3198 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3252 = destruct_flex_t t in
  match uu____3252 with
  | (t1,uv,k,args) ->
      let uu____3320 = pat_vars env [] args in
      (match uu____3320 with
       | FStar_Pervasives_Native.Some vars ->
           ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
       | uu____3376 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3424 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3447 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3451 -> false
let head_match: match_result -> match_result =
  fun uu___122_3454  ->
    match uu___122_3454 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3463 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3476 ->
          let uu____3477 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3477 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____3487 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3501 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3507 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____3529 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____3530 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____3531 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____3540 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____3548 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3565) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3571,uu____3572) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3602) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3617;
             FStar_Syntax_Syntax.index = uu____3618;
             FStar_Syntax_Syntax.sort = t2;_},uu____3620)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3627 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3628 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3629 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3637 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3653 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____3653
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
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____3672 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3672
            then FullMatch
            else
              (let uu____3674 =
                 let uu____3679 =
                   let uu____3681 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____3681 in
                 let uu____3682 =
                   let uu____3684 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____3684 in
                 (uu____3679, uu____3682) in
               MisMatch uu____3674)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3688),FStar_Syntax_Syntax.Tm_uinst (g,uu____3690)) ->
            let uu____3699 = head_matches env f g in
            FStar_All.pipe_right uu____3699 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3706),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3708)) ->
            let uu____3733 = FStar_Unionfind.equivalent uv uv' in
            if uu____3733
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3741),FStar_Syntax_Syntax.Tm_refine (y,uu____3743)) ->
            let uu____3752 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3752 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3754),uu____3755) ->
            let uu____3760 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3760 head_match
        | (uu____3761,FStar_Syntax_Syntax.Tm_refine (x,uu____3763)) ->
            let uu____3768 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3768 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3769,FStar_Syntax_Syntax.Tm_type
           uu____3770) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3771,FStar_Syntax_Syntax.Tm_arrow uu____3772) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3788),FStar_Syntax_Syntax.Tm_app (head',uu____3790))
            ->
            let uu____3819 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3819 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3821),uu____3822) ->
            let uu____3837 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3837 head_match
        | (uu____3838,FStar_Syntax_Syntax.Tm_app (head1,uu____3840)) ->
            let uu____3855 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3855 head_match
        | uu____3856 ->
            let uu____3859 =
              let uu____3864 = delta_depth_of_term env t11 in
              let uu____3866 = delta_depth_of_term env t21 in
              (uu____3864, uu____3866) in
            MisMatch uu____3859
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3902 = FStar_Syntax_Util.head_and_args t in
    match uu____3902 with
    | (head1,uu____3914) ->
        let uu____3929 =
          let uu____3930 = FStar_Syntax_Util.un_uinst head1 in
          uu____3930.FStar_Syntax_Syntax.n in
        (match uu____3929 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3935 =
               let uu____3936 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3936 FStar_Option.isSome in
             if uu____3935
             then
               let uu____3950 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3950
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
             else FStar_Pervasives_Native.None
         | uu____3953 -> FStar_Pervasives_Native.None) in
  let success d r t11 t21 =
    (r,
      (if d > (Prims.parse_int "0")
       then FStar_Pervasives_Native.Some (t11, t21)
       else FStar_Pervasives_Native.None)) in
  let fail r = (r, FStar_Pervasives_Native.None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch
        (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational
         ),uu____4021)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4031 =
             let uu____4036 = maybe_inline t11 in
             let uu____4038 = maybe_inline t21 in (uu____4036, uu____4038) in
           match uu____4031 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____4059,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4069 =
             let uu____4074 = maybe_inline t11 in
             let uu____4076 = maybe_inline t21 in (uu____4074, uu____4076) in
           match uu____4069 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2)
        when d1 = d2 ->
        let uu____4101 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4101 with
         | FStar_Pervasives_Native.None  -> fail r
         | FStar_Pervasives_Native.Some d ->
             let t12 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t11 in
             let t22 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
        let uu____4116 =
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
             let uu____4124 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4124)) in
        (match uu____4116 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4132 -> fail r
    | uu____4137 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4162 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4192 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4207 = FStar_Syntax_Util.type_u () in
      match uu____4207 with
      | (t,uu____4211) ->
          let uu____4212 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____4212
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4221 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4221 FStar_Pervasives_Native.fst
let rec decompose:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                   Prims.bool,(FStar_Syntax_Syntax.binder
                                                                 FStar_Pervasives_Native.option,
                                                                variance,
                                                                tc)
                                                                FStar_Pervasives_Native.tuple3
                                                                Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____4263 = head_matches env t1 t' in
        match uu____4263 with
        | MisMatch uu____4264 -> false
        | uu____4269 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4329,imp),T (t2,uu____4332)) -> (t2, imp)
                     | uu____4349 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4389  ->
                    match uu____4389 with
                    | (t2,uu____4397) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4427 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4427 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4480))::tcs2) ->
                       aux
                         (((let uu___146_4502 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4502.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4502.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4512 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_4543 =
                 match uu___123_4543 with
                 | [] ->
                     FStar_List.rev
                       ((FStar_Pervasives_Native.None, COVARIANT, (C c1)) ::
                       out)
                 | hd1::rest ->
                     decompose1
                       (((FStar_Pervasives_Native.Some hd1), CONTRAVARIANT,
                          (T
                             (((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4606 = decompose1 [] bs1 in
               (rebuild, matches, uu____4606))
      | uu____4634 ->
          let rebuild uu___124_4639 =
            match uu___124_4639 with
            | [] -> t1
            | uu____4641 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4660  ->
    match uu___125_4660 with
    | T (t,uu____4662) -> t
    | uu____4671 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4674  ->
    match uu___126_4674 with
    | T (t,uu____4676) -> FStar_Syntax_Syntax.as_arg t
    | uu____4685 -> failwith "Impossible"
let imitation_sub_probs:
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,FStar_Syntax_Syntax.formula)
              FStar_Pervasives_Native.tuple3
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
              | (uu____4754,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4773 = new_uvar r scope1 k in
                  (match uu____4773 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4785 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____4800 =
                         let uu____4801 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4801 in
                       ((T (gi_xs, mk_kind)), uu____4800))
              | (uu____4810,uu____4811,C uu____4812) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4899 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4910;
                         FStar_Syntax_Syntax.pos = uu____4911;
                         FStar_Syntax_Syntax.vars = uu____4912;_})
                        ->
                        let uu____4927 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4927 with
                         | (T (gi_xs,uu____4943),prob) ->
                             let uu____4953 =
                               let uu____4954 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4954 in
                             (uu____4953, [prob])
                         | uu____4956 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4966;
                         FStar_Syntax_Syntax.pos = uu____4967;
                         FStar_Syntax_Syntax.vars = uu____4968;_})
                        ->
                        let uu____4983 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4983 with
                         | (T (gi_xs,uu____4999),prob) ->
                             let uu____5009 =
                               let uu____5010 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5010 in
                             (uu____5009, [prob])
                         | uu____5012 -> failwith "impossible")
                    | (uu____5018,uu____5019,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5021;
                         FStar_Syntax_Syntax.pos = uu____5022;
                         FStar_Syntax_Syntax.vars = uu____5023;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (FStar_Pervasives_Native.None, INVARIANT,
                                    (T
                                       ((FStar_Pervasives_Native.fst t),
                                         generic_kind))))) in
                        let components1 =
                          (FStar_Pervasives_Native.None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components in
                        let uu____5097 =
                          let uu____5102 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5102 FStar_List.unzip in
                        (match uu____5097 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5131 =
                                 let uu____5132 =
                                   let uu____5135 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5135 un_T in
                                 let uu____5136 =
                                   let uu____5142 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5142
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5132;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5136;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5131 in
                             ((C gi_xs), sub_probs))
                    | uu____5147 ->
                        let uu____5154 = sub_prob scope1 args q in
                        (match uu____5154 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4899 with
                   | (tc,probs) ->
                       let uu____5172 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____5198,uu____5199) ->
                             let uu____5207 =
                               let uu____5211 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5211 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____5207)
                         | uu____5229 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____5172 with
                        | (bopt,scope2,args1) ->
                            let uu____5272 = aux scope2 args1 qs2 in
                            (match uu____5272 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5293 =
                                         let uu____5295 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____5295 in
                                       FStar_Syntax_Util.mk_conj_l uu____5293
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5308 =
                                         let uu____5310 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____5311 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____5310 :: uu____5311 in
                                       FStar_Syntax_Util.mk_conj_l uu____5308 in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
            aux scope ps qs
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ,
    FStar_Syntax_Syntax.args) FStar_Pervasives_Native.tuple4
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
     FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.arg Prims.list,
    (tc Prims.list -> FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ ->
                                                Prims.bool,(FStar_Syntax_Syntax.binder
                                                              FStar_Pervasives_Native.option,
                                                             variance,
                                                             tc)
                                                             FStar_Pervasives_Native.tuple3
                                                             Prims.list)
      FStar_Pervasives_Native.tuple3)
    FStar_Pervasives_Native.tuple3
let rigid_rigid: Prims.int = Prims.parse_int "0"
let flex_rigid_eq: Prims.int = Prims.parse_int "1"
let flex_refine_inner: Prims.int = Prims.parse_int "2"
let flex_refine: Prims.int = Prims.parse_int "3"
let flex_rigid: Prims.int = Prims.parse_int "4"
let rigid_flex: Prims.int = Prims.parse_int "5"
let refine_flex: Prims.int = Prims.parse_int "6"
let flex_flex: Prims.int = Prims.parse_int "7"
let compress_tprob wl p =
  let uu___147_5364 = p in
  let uu____5367 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5368 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5364.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5367;
    FStar_TypeChecker_Common.relation =
      (uu___147_5364.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5368;
    FStar_TypeChecker_Common.element =
      (uu___147_5364.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5364.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5364.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5364.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5364.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5364.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5378 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5378
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5383 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5397 = compress_prob wl pr in
        FStar_All.pipe_right uu____5397 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5403 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5403 with
           | (lh,uu____5416) ->
               let uu____5431 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5431 with
                | (rh,uu____5444) ->
                    let uu____5459 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5468,FStar_Syntax_Syntax.Tm_uvar uu____5469)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5488,uu____5489)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5500,FStar_Syntax_Syntax.Tm_uvar uu____5501)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5512,uu____5513)
                          ->
                          let uu____5522 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5522 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____5562 ->
                                    let rank =
                                      let uu____5569 = is_top_level_prob prob in
                                      if uu____5569
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5571 =
                                      let uu___148_5574 = tp in
                                      let uu____5577 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5574.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5574.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5574.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5577;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5574.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5574.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5574.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5574.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5574.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5574.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5571)))
                      | (uu____5587,FStar_Syntax_Syntax.Tm_uvar uu____5588)
                          ->
                          let uu____5597 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5597 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____5637 ->
                                    let uu____5643 =
                                      let uu___149_5648 = tp in
                                      let uu____5651 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5648.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5651;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5648.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5648.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5648.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5648.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5648.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5648.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5648.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5648.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5643)))
                      | (uu____5667,uu____5668) -> (rigid_rigid, tp) in
                    (match uu____5459 with
                     | (rank,tp1) ->
                         let uu____5679 =
                           FStar_All.pipe_right
                             (let uu___150_5682 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5682.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5682.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5682.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5682.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5682.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5682.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5682.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5682.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5682.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5679))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5688 =
            FStar_All.pipe_right
              (let uu___151_5691 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5691.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5691.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5691.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5691.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5691.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5691.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5691.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5691.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5691.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5688)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____5723 probs =
      match uu____5723 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5753 = rank wl hd1 in
               (match uu____5753 with
                | (rank1,hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out (m :: tl1)), rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2),
                                 out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2), (m
                                 :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1)) in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
      wl.attempting
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
    match projectee with | UDeferred _0 -> true | uu____5818 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5830 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5842 -> false
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
                        let uu____5879 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5879 with
                        | (k,uu____5883) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5888 -> false)))
            | uu____5889 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5932 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5932 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5935 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5941 =
                     let uu____5942 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5943 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5942
                       uu____5943 in
                   UFailed uu____5941)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5959 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5959 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
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
            | uu____5980 ->
                let uu____5983 =
                  let uu____5984 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5985 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5984
                    uu____5985 msg in
                UFailed uu____5983 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5986,uu____5987) ->
              let uu____5988 =
                let uu____5989 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5990 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5989 uu____5990 in
              failwith uu____5988
          | (FStar_Syntax_Syntax.U_unknown ,uu____5991) ->
              let uu____5992 =
                let uu____5993 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5994 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5993 uu____5994 in
              failwith uu____5992
          | (uu____5995,FStar_Syntax_Syntax.U_bvar uu____5996) ->
              let uu____5997 =
                let uu____5998 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5999 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5998 uu____5999 in
              failwith uu____5997
          | (uu____6000,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6001 =
                let uu____6002 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6003 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6002 uu____6003 in
              failwith uu____6001
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6015 = FStar_Unionfind.equivalent v1 v2 in
              if uu____6015
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6026 = occurs_univ v1 u3 in
              if uu____6026
              then
                let uu____6027 =
                  let uu____6028 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6029 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6028 uu____6029 in
                try_umax_components u11 u21 uu____6027
              else
                (let uu____6031 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6031)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6039 = occurs_univ v1 u3 in
              if uu____6039
              then
                let uu____6040 =
                  let uu____6041 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6042 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6041 uu____6042 in
                try_umax_components u11 u21 uu____6040
              else
                (let uu____6044 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6044)
          | (FStar_Syntax_Syntax.U_max uu____6047,uu____6048) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6053 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6053
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6055,FStar_Syntax_Syntax.U_max uu____6056) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6061 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6061
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6063,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6064,FStar_Syntax_Syntax.U_name
             uu____6065) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6066) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6067) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6068,FStar_Syntax_Syntax.U_succ
             uu____6069) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6070,FStar_Syntax_Syntax.U_zero
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
  let uu____6132 = bc1 in
  match uu____6132 with
  | (bs1,mk_cod1) ->
      let uu____6157 = bc2 in
      (match uu____6157 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6204 = FStar_Util.first_N n1 bs in
             match uu____6204 with
             | (bs3,rest) ->
                 let uu____6218 = mk_cod rest in (bs3, uu____6218) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6236 =
               let uu____6240 = mk_cod1 [] in (bs1, uu____6240) in
             let uu____6242 =
               let uu____6246 = mk_cod2 [] in (bs2, uu____6246) in
             (uu____6236, uu____6242)
           else
             if l1 > l2
             then
               (let uu____6268 = curry l2 bs1 mk_cod1 in
                let uu____6275 =
                  let uu____6279 = mk_cod2 [] in (bs2, uu____6279) in
                (uu____6268, uu____6275))
             else
               (let uu____6288 =
                  let uu____6292 = mk_cod1 [] in (bs1, uu____6292) in
                let uu____6294 = curry l1 bs2 mk_cod2 in
                (uu____6288, uu____6294)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6398 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6398
       then
         let uu____6399 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6399
       else ());
      (let uu____6401 = next_prob probs in
       match uu____6401 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6414 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6414.wl_deferred);
               ctr = (uu___152_6414.ctr);
               defer_ok = (uu___152_6414.defer_ok);
               smt_ok = (uu___152_6414.smt_ok);
               tcenv = (uu___152_6414.tcenv)
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
                  let uu____6421 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6421 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6425 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6425 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____6429,uu____6430) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6439 ->
                let uu____6444 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6472  ->
                          match uu____6472 with
                          | (c,uu____6477,uu____6478) -> c < probs.ctr)) in
                (match uu____6444 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6500 =
                            FStar_List.map
                              (fun uu____6506  ->
                                 match uu____6506 with
                                 | (uu____6512,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6500
                      | uu____6515 ->
                          let uu____6520 =
                            let uu___153_6521 = probs in
                            let uu____6522 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6531  ->
                                      match uu____6531 with
                                      | (uu____6535,uu____6536,y) -> y)) in
                            {
                              attempting = uu____6522;
                              wl_deferred = rest;
                              ctr = (uu___153_6521.ctr);
                              defer_ok = (uu___153_6521.defer_ok);
                              smt_ok = (uu___153_6521.smt_ok);
                              tcenv = (uu___153_6521.tcenv)
                            } in
                          solve env uu____6520))))
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
            let uu____6543 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6543 with
            | USolved wl1 ->
                let uu____6545 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____6545
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
                  let uu____6579 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6579 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6582 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6590;
                  FStar_Syntax_Syntax.pos = uu____6591;
                  FStar_Syntax_Syntax.vars = uu____6592;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6595;
                  FStar_Syntax_Syntax.pos = uu____6596;
                  FStar_Syntax_Syntax.vars = uu____6597;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6609,uu____6610) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6615,FStar_Syntax_Syntax.Tm_uinst uu____6616) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6621 -> USolved wl
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
            ((let uu____6629 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6629
              then
                let uu____6630 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6630 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6638 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6638
         then
           let uu____6639 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6639
         else ());
        (let uu____6641 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6641 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6683 = head_matches_delta env () t1 t2 in
               match uu____6683 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6705 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____6731 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____6740 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6741 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6740, uu____6741)
                          | FStar_Pervasives_Native.None  ->
                              let uu____6744 = FStar_Syntax_Subst.compress t1 in
                              let uu____6745 = FStar_Syntax_Subst.compress t2 in
                              (uu____6744, uu____6745) in
                        (match uu____6731 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6767 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6767 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6790 =
                                    let uu____6796 =
                                      let uu____6799 =
                                        let uu____6802 =
                                          let uu____6803 =
                                            let uu____6808 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6808) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6803 in
                                        FStar_Syntax_Syntax.mk uu____6802 in
                                      uu____6799 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6821 =
                                      let uu____6823 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6823] in
                                    (uu____6796, uu____6821) in
                                  FStar_Pervasives_Native.Some uu____6790
                              | (uu____6832,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6834)) ->
                                  let uu____6839 =
                                    let uu____6843 =
                                      let uu____6845 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6845] in
                                    (t11, uu____6843) in
                                  FStar_Pervasives_Native.Some uu____6839
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6851),uu____6852) ->
                                  let uu____6857 =
                                    let uu____6861 =
                                      let uu____6863 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6863] in
                                    (t21, uu____6861) in
                                  FStar_Pervasives_Native.Some uu____6857
                              | uu____6868 ->
                                  let uu____6871 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6871 with
                                   | (head1,uu____6886) ->
                                       let uu____6901 =
                                         let uu____6902 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6902.FStar_Syntax_Syntax.n in
                                       (match uu____6901 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6909;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6911;_}
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
                                        | uu____6920 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6929) ->
                  let uu____6942 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6951  ->
                            match uu___127_6951 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____6956 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6956 with
                                      | (u',uu____6967) ->
                                          let uu____6982 =
                                            let uu____6983 = whnf env u' in
                                            uu____6983.FStar_Syntax_Syntax.n in
                                          (match uu____6982 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6987) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____7003 -> false))
                                 | uu____7004 -> false)
                            | uu____7006 -> false)) in
                  (match uu____6942 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7027 tps =
                         match uu____7027 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7054 =
                                    let uu____7059 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7059 in
                                  (match uu____7054 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____7078 -> FStar_Pervasives_Native.None) in
                       let uu____7083 =
                         let uu____7088 =
                           let uu____7092 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7092, []) in
                         make_lower_bound uu____7088 lower_bounds in
                       (match uu____7083 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____7099 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7099
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             FStar_Pervasives_Native.None)
                        | FStar_Pervasives_Native.Some (lhs_bound,sub_probs)
                            ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs
                                FStar_Pervasives_Native.None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements" in
                            ((let uu____7112 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7112
                              then
                                let wl' =
                                  let uu___154_7114 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7114.wl_deferred);
                                    ctr = (uu___154_7114.ctr);
                                    defer_ok = (uu___154_7114.defer_ok);
                                    smt_ok = (uu___154_7114.smt_ok);
                                    tcenv = (uu___154_7114.tcenv)
                                  } in
                                let uu____7115 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7115
                              else ());
                             (let uu____7117 =
                                solve_t env eq_prob
                                  (let uu___155_7118 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7118.wl_deferred);
                                     ctr = (uu___155_7118.ctr);
                                     defer_ok = (uu___155_7118.defer_ok);
                                     smt_ok = (uu___155_7118.smt_ok);
                                     tcenv = (uu___155_7118.tcenv)
                                   }) in
                              match uu____7117 with
                              | Success uu____7120 ->
                                  let wl1 =
                                    let uu___156_7122 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7122.wl_deferred);
                                      ctr = (uu___156_7122.ctr);
                                      defer_ok = (uu___156_7122.defer_ok);
                                      smt_ok = (uu___156_7122.smt_ok);
                                      tcenv = (uu___156_7122.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____7124 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____7127 -> FStar_Pervasives_Native.None))))
              | uu____7128 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7135 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7135
         then
           let uu____7136 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7136
         else ());
        (let uu____7138 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7138 with
         | (u,args) ->
             let uu____7165 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7165 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7196 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7196 with
                    | (h1,args1) ->
                        let uu____7224 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7224 with
                         | (h2,uu____7237) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7256 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7256
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7269 =
                                          let uu____7271 =
                                            let uu____7272 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7272 in
                                          [uu____7271] in
                                        FStar_Pervasives_Native.Some
                                          uu____7269))
                                  else FStar_Pervasives_Native.None
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7294 =
                                          let uu____7296 =
                                            let uu____7297 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7297 in
                                          [uu____7296] in
                                        FStar_Pervasives_Native.Some
                                          uu____7294))
                                  else FStar_Pervasives_Native.None
                              | uu____7305 -> FStar_Pervasives_Native.None)) in
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
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let uu____7371 =
                               let uu____7377 =
                                 let uu____7380 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7380 in
                               (uu____7377, m1) in
                             FStar_Pervasives_Native.Some uu____7371)
                    | (uu____7389,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7391)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7423),uu____7424) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____7455 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7489) ->
                       let uu____7502 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7511  ->
                                 match uu___128_7511 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____7516 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7516 with
                                           | (u',uu____7527) ->
                                               let uu____7542 =
                                                 let uu____7543 = whnf env u' in
                                                 uu____7543.FStar_Syntax_Syntax.n in
                                               (match uu____7542 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7547) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7563 -> false))
                                      | uu____7564 -> false)
                                 | uu____7566 -> false)) in
                       (match uu____7502 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7591 tps =
                              match uu____7591 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7632 =
                                         let uu____7639 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7639 in
                                       (match uu____7632 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7674 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____7681 =
                              let uu____7688 =
                                let uu____7694 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7694, []) in
                              make_upper_bound uu____7688 upper_bounds in
                            (match uu____7681 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____7703 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7703
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  FStar_Pervasives_Native.None)
                             | FStar_Pervasives_Native.Some
                                 (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     FStar_Pervasives_Native.None
                                     tp.FStar_TypeChecker_Common.loc
                                     "joining refinements" in
                                 ((let uu____7722 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7722
                                   then
                                     let wl' =
                                       let uu___157_7724 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7724.wl_deferred);
                                         ctr = (uu___157_7724.ctr);
                                         defer_ok = (uu___157_7724.defer_ok);
                                         smt_ok = (uu___157_7724.smt_ok);
                                         tcenv = (uu___157_7724.tcenv)
                                       } in
                                     let uu____7725 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7725
                                   else ());
                                  (let uu____7727 =
                                     solve_t env eq_prob
                                       (let uu___158_7728 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7728.wl_deferred);
                                          ctr = (uu___158_7728.ctr);
                                          defer_ok = (uu___158_7728.defer_ok);
                                          smt_ok = (uu___158_7728.smt_ok);
                                          tcenv = (uu___158_7728.tcenv)
                                        }) in
                                   match uu____7727 with
                                   | Success uu____7730 ->
                                       let wl1 =
                                         let uu___159_7732 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7732.wl_deferred);
                                           ctr = (uu___159_7732.ctr);
                                           defer_ok =
                                             (uu___159_7732.defer_ok);
                                           smt_ok = (uu___159_7732.smt_ok);
                                           tcenv = (uu___159_7732.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____7734 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____7737 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____7738 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7803 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7803
                      then
                        let uu____7804 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7804
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7836 = hd1 in
                      let uu____7837 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7836.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7836.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7837
                      } in
                    let hd21 =
                      let uu___161_7841 = hd2 in
                      let uu____7842 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7841.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7841.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7842
                      } in
                    let prob =
                      let uu____7846 =
                        let uu____7849 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7849 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7846 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7857 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7857 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7860 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7860 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7878 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____7881 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7878 uu____7881 in
                         ((let uu____7887 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7887
                           then
                             let uu____7888 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7889 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7888 uu____7889
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7904 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7910 = aux scope env [] bs1 bs2 in
              match uu____7910 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7926 = compress_tprob wl problem in
        solve_t' env uu____7926 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7959 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7959 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7976,uu____7977) ->
                   let may_relate head3 =
                     let uu____7992 =
                       let uu____7993 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7993.FStar_Syntax_Syntax.n in
                     match uu____7992 with
                     | FStar_Syntax_Syntax.Tm_name uu____7996 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7997 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8014 -> false in
                   let uu____8015 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8015
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
                            | FStar_Pervasives_Native.Some t ->
                                FStar_Syntax_Util.mk_has_type t11 t t21
                            | FStar_Pervasives_Native.None  ->
                                let x =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None t11 in
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11 in
                                let uu____8032 =
                                  let uu____8033 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8033 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8032 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8035 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____8035
                   else giveup env1 "head mismatch" orig
               | (uu____8037,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8045 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8045.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8045.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8045.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8045.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8045.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8045.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8045.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8045.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8046,FStar_Pervasives_Native.None ) ->
                   ((let uu____8053 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8053
                     then
                       let uu____8054 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8055 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8056 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8057 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8054
                         uu____8055 uu____8056 uu____8057
                     else ());
                    (let uu____8059 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8059 with
                     | (head11,args1) ->
                         let uu____8085 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8085 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8125 =
                                  let uu____8126 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8127 = args_to_string args1 in
                                  let uu____8128 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8129 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8126 uu____8127 uu____8128
                                    uu____8129 in
                                giveup env1 uu____8125 orig
                              else
                                (let uu____8131 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8134 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8134 = FStar_Syntax_Util.Equal) in
                                 if uu____8131
                                 then
                                   let uu____8135 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8135 with
                                   | USolved wl2 ->
                                       let uu____8137 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____8137
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8141 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8141 with
                                    | (base1,refinement1) ->
                                        let uu____8167 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8167 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____8221 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8221 with
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
                                                           (fun uu____8231 
                                                              ->
                                                              fun uu____8232 
                                                                ->
                                                                match 
                                                                  (uu____8231,
                                                                    uu____8232)
                                                                with
                                                                | ((a,uu____8242),
                                                                   (a',uu____8244))
                                                                    ->
                                                                    let uu____8249
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index" in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_49  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_49)
                                                                    uu____8249)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8255 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8255 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8259 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_8292 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8292.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8312 = p in
          match uu____8312 with
          | (((u,k),xs,c),ps,(h,uu____8323,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8372 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8372 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8386 = h gs_xs in
                     let uu____8387 =
                       let uu____8394 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____8394
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____8386 uu____8387 in
                   ((let uu____8425 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8425
                     then
                       let uu____8426 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8427 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8428 = FStar_Syntax_Print.term_to_string im in
                       let uu____8429 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8430 =
                         let uu____8431 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8431
                           (FStar_String.concat ", ") in
                       let uu____8434 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8426 uu____8427 uu____8428 uu____8429
                         uu____8430 uu____8434
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_8452 =
          match uu___129_8452 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8481 = p in
          match uu____8481 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8539 = FStar_List.nth ps i in
              (match uu____8539 with
               | (pi,uu____8542) ->
                   let uu____8547 = FStar_List.nth xs i in
                   (match uu____8547 with
                    | (xi,uu____8554) ->
                        let rec gs k =
                          let uu____8563 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8563 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8615)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8623 = new_uvar r xs k_a in
                                    (match uu____8623 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (FStar_Pervasives_Native.Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1 in
                                         let uu____8642 = aux subst2 tl1 in
                                         (match uu____8642 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8657 =
                                                let uu____8659 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8659 :: gi_xs' in
                                              let uu____8660 =
                                                let uu____8662 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8662 :: gi_ps' in
                                              (uu____8657, uu____8660))) in
                              aux [] bs in
                        let uu____8665 =
                          let uu____8666 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8666 in
                        if uu____8665
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____8669 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8669 with
                           | (g_xs,uu____8676) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8683 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     FStar_Pervasives_Native.None r in
                                 let uu____8688 =
                                   let uu____8695 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8695
                                     (fun _0_53  ->
                                        FStar_Pervasives_Native.Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8683
                                   uu____8688 in
                               let sub1 =
                                 let uu____8726 =
                                   let uu____8729 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       FStar_Pervasives_Native.None r in
                                   let uu____8736 =
                                     let uu____8739 =
                                       FStar_List.map
                                         (fun uu____8745  ->
                                            match uu____8745 with
                                            | (uu____8750,uu____8751,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8739 in
                                   mk_problem (p_scope orig) orig uu____8729
                                     (p_rel orig) uu____8736
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8726 in
                               ((let uu____8761 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8761
                                 then
                                   let uu____8762 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8763 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8762 uu____8763
                                 else ());
                                (let wl2 =
                                   let uu____8766 =
                                     let uu____8768 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____8768 in
                                   solve_prob orig uu____8766
                                     [TERM (u, proj)] wl1 in
                                 let uu____8773 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  ->
                                      FStar_Pervasives_Native.Some _0_55)
                                   uu____8773))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8797 = lhs in
          match uu____8797 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8820 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8820 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8842 =
                        let uu____8868 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8868) in
                      FStar_Pervasives_Native.Some uu____8842
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8951 =
                           let uu____8955 =
                             let uu____8956 = FStar_Syntax_Subst.compress k in
                             uu____8956.FStar_Syntax_Syntax.n in
                           (uu____8955, args) in
                         match uu____8951 with
                         | (uu____8963,[]) ->
                             let uu____8965 =
                               let uu____8971 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8971) in
                             FStar_Pervasives_Native.Some uu____8965
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8982,uu____8983) ->
                             let uu____8994 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8994 with
                              | (uv1,uv_args) ->
                                  let uu____9023 =
                                    let uu____9024 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9024.FStar_Syntax_Syntax.n in
                                  (match uu____9023 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9031) ->
                                       let uu____9044 =
                                         pat_vars env [] uv_args in
                                       (match uu____9044 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9058  ->
                                                      let uu____9059 =
                                                        let uu____9060 =
                                                          let uu____9061 =
                                                            let uu____9064 =
                                                              let uu____9065
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9065
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9064 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9061 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9060 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9059)) in
                                            let c1 =
                                              let uu____9071 =
                                                let uu____9072 =
                                                  let uu____9075 =
                                                    let uu____9076 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9076
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9075 in
                                                FStar_Pervasives_Native.fst
                                                  uu____9072 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9071 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9085 =
                                                let uu____9092 =
                                                  let uu____9098 =
                                                    let uu____9099 =
                                                      let uu____9102 =
                                                        let uu____9103 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9103
                                                          FStar_Pervasives_Native.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9102 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9099 in
                                                  FStar_Util.Inl uu____9098 in
                                                FStar_Pervasives_Native.Some
                                                  uu____9092 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9085 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9126 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9129,uu____9130)
                             ->
                             let uu____9142 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9142 with
                              | (uv1,uv_args) ->
                                  let uu____9171 =
                                    let uu____9172 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9172.FStar_Syntax_Syntax.n in
                                  (match uu____9171 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9179) ->
                                       let uu____9192 =
                                         pat_vars env [] uv_args in
                                       (match uu____9192 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9206  ->
                                                      let uu____9207 =
                                                        let uu____9208 =
                                                          let uu____9209 =
                                                            let uu____9212 =
                                                              let uu____9213
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9213
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9212 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9209 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9208 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9207)) in
                                            let c1 =
                                              let uu____9219 =
                                                let uu____9220 =
                                                  let uu____9223 =
                                                    let uu____9224 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9224
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9223 in
                                                FStar_Pervasives_Native.fst
                                                  uu____9220 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9219 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9233 =
                                                let uu____9240 =
                                                  let uu____9246 =
                                                    let uu____9247 =
                                                      let uu____9250 =
                                                        let uu____9251 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9251
                                                          FStar_Pervasives_Native.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9250 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9247 in
                                                  FStar_Util.Inl uu____9246 in
                                                FStar_Pervasives_Native.Some
                                                  uu____9240 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9233 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9274 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9279)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9305 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9305
                                 (fun _0_56  ->
                                    FStar_Pervasives_Native.Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9324 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9324 with
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
                                                    FStar_Pervasives_Native.Some
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
                                              (rest, c1)))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9427 =
                                        let uu____9430 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9430 in
                                      FStar_All.pipe_right uu____9427
                                        (fun _0_57  ->
                                           FStar_Pervasives_Native.Some _0_57))
                         | uu____9438 ->
                             let uu____9442 =
                               let uu____9443 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9447 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9448 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9443 uu____9447 uu____9448 in
                             failwith uu____9442 in
                       let uu____9452 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9452
                         (fun uu____9480  ->
                            match uu____9480 with
                            | (xs1,c1) ->
                                let uu____9508 =
                                  let uu____9531 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9531) in
                                FStar_Pervasives_Native.Some uu____9508)) in
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
                     let uu____9603 = imitate orig env wl1 st in
                     match uu____9603 with
                     | Failed uu____9608 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9614 = project orig env wl1 i st in
                      match uu____9614 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____9621) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9635 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9635 with
                | (hd1,uu____9646) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9661 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9669 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9670 -> true
                     | uu____9685 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9688 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9688
                         then true
                         else
                           ((let uu____9691 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9691
                             then
                               let uu____9692 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9692
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9700 =
                    let uu____9703 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9703
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____9700 FStar_Syntax_Free.names in
                let uu____9734 = FStar_Util.set_is_empty fvs_hd in
                if uu____9734
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____9743 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____9743 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9751 =
                            let uu____9752 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____9752 in
                          giveup_or_defer1 orig uu____9751
                        else
                          (let uu____9754 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____9754
                           then
                             let uu____9755 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____9755
                              then
                                let uu____9756 = subterms args_lhs in
                                imitate' orig env wl1 uu____9756
                              else
                                ((let uu____9760 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9760
                                  then
                                    let uu____9761 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9762 = names_to_string fvs1 in
                                    let uu____9763 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9761 uu____9762 uu____9763
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9768 ->
                                        let uu____9769 = sn_binders env vars in
                                        u_abs k_uv uu____9769 t21 in
                                  let wl2 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None
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
                               (let uu____9778 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9778
                                then
                                  ((let uu____9780 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9780
                                    then
                                      let uu____9781 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9782 = names_to_string fvs1 in
                                      let uu____9783 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9781 uu____9782 uu____9783
                                    else ());
                                   (let uu____9785 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9785
                                      (- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | FStar_Pervasives_Native.None  when patterns_only ->
                   giveup env "not a pattern" orig
               | FStar_Pervasives_Native.None  ->
                   if wl1.defer_ok
                   then solve env (defer "not a pattern" orig wl1)
                   else
                     (let uu____9796 =
                        let uu____9797 = FStar_Syntax_Free.names t1 in
                        check_head uu____9797 t2 in
                      if uu____9796
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9801 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9801
                          then
                            let uu____9802 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9802
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9805 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9805 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9847 =
               match uu____9847 with
               | (t,u,k,args) ->
                   let uu____9877 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9877 with
                    | (all_formals,uu____9888) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9980  ->
                                        match uu____9980 with
                                        | (x,imp) ->
                                            let uu____9987 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9987, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9995 = FStar_Syntax_Util.type_u () in
                                match uu____9995 with
                                | (t1,uu____9999) ->
                                    let uu____10000 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____10000 in
                              let uu____10003 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10003 with
                               | (t',tm_u1) ->
                                   let uu____10010 = destruct_flex_t t' in
                                   (match uu____10010 with
                                    | (uu____10030,u1,k1,uu____10033) ->
                                        let sol =
                                          let uu____10061 =
                                            let uu____10066 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____10066) in
                                          TERM uu____10061 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1)
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10126 = pat_var_opt env pat_args hd1 in
                              (match uu____10126 with
                               | FStar_Pervasives_Native.None  ->
                                   aux pat_args pattern_vars pattern_var_set
                                     formals1 tl1
                               | FStar_Pervasives_Native.Some y ->
                                   let maybe_pat =
                                     match xs_opt with
                                     | FStar_Pervasives_Native.None  -> true
                                     | FStar_Pervasives_Native.Some xs ->
                                         FStar_All.pipe_right xs
                                           (FStar_Util.for_some
                                              (fun uu____10155  ->
                                                 match uu____10155 with
                                                 | (x,uu____10159) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x
                                                       (FStar_Pervasives_Native.fst
                                                          y))) in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                                      let uu____10165 =
                                        let uu____10166 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10166 in
                                      if uu____10165
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10170 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10170 formals1
                                           tl1)))
                          | uu____10176 -> failwith "Impossible" in
                        let uu____10187 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10187 all_formals args) in
             let solve_both_pats wl1 uu____10235 uu____10236 r =
               match (uu____10235, uu____10236) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10390 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____10390
                   then
                     let uu____10394 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____10394
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10409 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10409
                       then
                         let uu____10410 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10411 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10412 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10413 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10414 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10410 uu____10411 uu____10412 uu____10413
                           uu____10414
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10456 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10456 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10464 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10464 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10494 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10494 in
                                  let uu____10497 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10497 k3)
                           else
                             (let uu____10500 =
                                let uu____10501 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10502 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10503 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10501 uu____10502 uu____10503 in
                              failwith uu____10500) in
                       let uu____10504 =
                         let uu____10510 =
                           let uu____10518 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10518 in
                         match uu____10510 with
                         | (bs,k1') ->
                             let uu____10536 =
                               let uu____10544 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10544 in
                             (match uu____10536 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10565 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10565 in
                                  let uu____10570 =
                                    let uu____10573 =
                                      let uu____10574 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10574.FStar_Syntax_Syntax.n in
                                    let uu____10577 =
                                      let uu____10578 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10578.FStar_Syntax_Syntax.n in
                                    (uu____10573, uu____10577) in
                                  (match uu____10570 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10586,uu____10587) ->
                                       (k1', [sub_prob])
                                   | (uu____10591,FStar_Syntax_Syntax.Tm_type
                                      uu____10592) -> (k2', [sub_prob])
                                   | uu____10596 ->
                                       let uu____10599 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10599 with
                                        | (t,uu____10608) ->
                                            let uu____10609 = new_uvar r zs t in
                                            (match uu____10609 with
                                             | (k_zs,uu____10618) ->
                                                 let kprob =
                                                   let uu____10620 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10620 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10504 with
                       | (k_u',sub_probs) ->
                           let uu____10634 =
                             let uu____10642 =
                               let uu____10643 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____10643 in
                             let uu____10648 =
                               let uu____10651 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10651 in
                             let uu____10654 =
                               let uu____10657 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10657 in
                             (uu____10642, uu____10648, uu____10654) in
                           (match uu____10634 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10676 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10676 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10700 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____10700
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10707 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10707 with
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
                                                    solve_prob orig
                                                      FStar_Pervasives_Native.None
                                                      [sol1; sol2] wl1 in
                                                  solve env
                                                    (attempt sub_probs wl2)))))))) in
             let solve_one_pat uu____10759 uu____10760 =
               match (uu____10759, uu____10760) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10864 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10864
                     then
                       let uu____10865 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10866 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10865 uu____10866
                     else ());
                    (let uu____10868 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____10868
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10878  ->
                              fun uu____10879  ->
                                match (uu____10878, uu____10879) with
                                | ((a,uu____10889),(t21,uu____10891)) ->
                                    let uu____10896 =
                                      let uu____10899 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10899
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10896
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10903 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10903 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10913 = occurs_check env wl (u1, k1) t21 in
                        match uu____10913 with
                        | (occurs_ok,uu____10922) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10927 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10927
                            then
                              let sol =
                                let uu____10929 =
                                  let uu____10934 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10934) in
                                TERM uu____10929 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____10947 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10947
                               then
                                 let uu____10948 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10948 with
                                 | (sol,(uu____10962,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10972 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10972
                                       then
                                         let uu____10973 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10973
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10978 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10980 = lhs in
             match uu____10980 with
             | (t1,u1,k1,args1) ->
                 let uu____10985 = rhs in
                 (match uu____10985 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1 in
                      let maybe_pat_vars2 = pat_vars env [] args2 in
                      let r = t2.FStar_Syntax_Syntax.pos in
                      (match (maybe_pat_vars1, maybe_pat_vars2) with
                       | (FStar_Pervasives_Native.Some
                          xs,FStar_Pervasives_Native.Some ys) ->
                           solve_both_pats wl (u1, k1, xs, args1)
                             (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                       | (FStar_Pervasives_Native.Some
                          xs,FStar_Pervasives_Native.None ) ->
                           solve_one_pat (t1, u1, k1, xs) rhs
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.Some ys) ->
                           solve_one_pat (t2, u2, k2, ys) lhs
                       | uu____11011 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11017 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____11017 with
                              | (sol,uu____11024) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____11027 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____11027
                                    then
                                      let uu____11028 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11028
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11033 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____11035 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____11035
        then
          let uu____11036 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____11036
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____11040 = FStar_Util.physical_equality t1 t2 in
           if uu____11040
           then
             let uu____11041 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____11041
           else
             ((let uu____11044 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____11044
               then
                 let uu____11045 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____11045
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11048,uu____11049) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11050,FStar_Syntax_Syntax.Tm_bvar uu____11051) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_11091 =
                     match uu___130_11091 with
                     | [] -> c
                     | bs ->
                         let uu____11105 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11105 in
                   let uu____11115 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11115 with
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
                                   let uu____11201 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11201
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11203 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11203))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11280 =
                     match uu___131_11280 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11315 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11315 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11398 =
                                   let uu____11401 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11402 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11401
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11402 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11398))
               | (FStar_Syntax_Syntax.Tm_abs uu____11405,uu____11406) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11429 -> true
                     | uu____11444 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11472 =
                     let uu____11483 = maybe_eta t1 in
                     let uu____11488 = maybe_eta t2 in
                     (uu____11483, uu____11488) in
                   (match uu____11472 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11519 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11519.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11519.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11519.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11519.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11519.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11519.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11519.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11519.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11538 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11538
                        then
                          let uu____11539 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11539 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11560 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11560
                        then
                          let uu____11561 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11561 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11566 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11577,FStar_Syntax_Syntax.Tm_abs uu____11578) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11601 -> true
                     | uu____11616 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11644 =
                     let uu____11655 = maybe_eta t1 in
                     let uu____11660 = maybe_eta t2 in
                     (uu____11655, uu____11660) in
                   (match uu____11644 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11691 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11691.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11691.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11691.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11691.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11691.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11691.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11691.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11691.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11710 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11710
                        then
                          let uu____11711 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11711 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11732 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11732
                        then
                          let uu____11733 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11733 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11738 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11749,FStar_Syntax_Syntax.Tm_refine uu____11750) ->
                   let uu____11759 = as_refinement env wl t1 in
                   (match uu____11759 with
                    | (x1,phi1) ->
                        let uu____11764 = as_refinement env wl t2 in
                        (match uu____11764 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11770 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11770 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11803 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11803
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11807 =
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
                                 let uu____11813 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____11813 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11820 =
                                   let uu____11823 =
                                     let uu____11824 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11824 :: (p_scope orig) in
                                   mk_problem uu____11823 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11820 in
                               let uu____11827 =
                                 solve env1
                                   (let uu___165_11828 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_11828.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_11828.smt_ok);
                                      tcenv = (uu___165_11828.tcenv)
                                    }) in
                               (match uu____11827 with
                                | Failed uu____11832 -> fallback ()
                                | Success uu____11835 ->
                                    let guard =
                                      let uu____11839 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____11842 =
                                        let uu____11843 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____11843
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11839
                                        uu____11842 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___166_11850 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_11850.attempting);
                                        wl_deferred =
                                          (uu___166_11850.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_11850.defer_ok);
                                        smt_ok = (uu___166_11850.smt_ok);
                                        tcenv = (uu___166_11850.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11852,FStar_Syntax_Syntax.Tm_uvar uu____11853) ->
                   let uu____11870 = destruct_flex_t t1 in
                   let uu____11871 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11870 uu____11871
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11872;
                     FStar_Syntax_Syntax.tk = uu____11873;
                     FStar_Syntax_Syntax.pos = uu____11874;
                     FStar_Syntax_Syntax.vars = uu____11875;_},uu____11876),FStar_Syntax_Syntax.Tm_uvar
                  uu____11877) ->
                   let uu____11908 = destruct_flex_t t1 in
                   let uu____11909 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11908 uu____11909
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11910,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11911;
                     FStar_Syntax_Syntax.tk = uu____11912;
                     FStar_Syntax_Syntax.pos = uu____11913;
                     FStar_Syntax_Syntax.vars = uu____11914;_},uu____11915))
                   ->
                   let uu____11946 = destruct_flex_t t1 in
                   let uu____11947 = destruct_flex_t t2 in
                   flex_flex1 orig uu____11946 uu____11947
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11948;
                     FStar_Syntax_Syntax.tk = uu____11949;
                     FStar_Syntax_Syntax.pos = uu____11950;
                     FStar_Syntax_Syntax.vars = uu____11951;_},uu____11952),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11953;
                     FStar_Syntax_Syntax.tk = uu____11954;
                     FStar_Syntax_Syntax.pos = uu____11955;
                     FStar_Syntax_Syntax.vars = uu____11956;_},uu____11957))
                   ->
                   let uu____12002 = destruct_flex_t t1 in
                   let uu____12003 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12002 uu____12003
               | (FStar_Syntax_Syntax.Tm_uvar uu____12004,uu____12005) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12014 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12014 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12018;
                     FStar_Syntax_Syntax.tk = uu____12019;
                     FStar_Syntax_Syntax.pos = uu____12020;
                     FStar_Syntax_Syntax.vars = uu____12021;_},uu____12022),uu____12023)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12046 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12046 t2 wl
               | (uu____12050,FStar_Syntax_Syntax.Tm_uvar uu____12051) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12060,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12061;
                     FStar_Syntax_Syntax.tk = uu____12062;
                     FStar_Syntax_Syntax.pos = uu____12063;
                     FStar_Syntax_Syntax.vars = uu____12064;_},uu____12065))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12088,FStar_Syntax_Syntax.Tm_type uu____12089) ->
                   solve_t' env
                     (let uu___167_12098 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12098.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12098.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12098.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12098.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12098.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12098.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12098.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12098.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12098.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12099;
                     FStar_Syntax_Syntax.tk = uu____12100;
                     FStar_Syntax_Syntax.pos = uu____12101;
                     FStar_Syntax_Syntax.vars = uu____12102;_},uu____12103),FStar_Syntax_Syntax.Tm_type
                  uu____12104) ->
                   solve_t' env
                     (let uu___167_12127 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12127.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12127.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12127.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12127.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12127.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12127.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12127.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12127.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12127.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12128,FStar_Syntax_Syntax.Tm_arrow uu____12129) ->
                   solve_t' env
                     (let uu___167_12145 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12145.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12145.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12145.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12145.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12145.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12145.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12145.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12145.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12145.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12146;
                     FStar_Syntax_Syntax.tk = uu____12147;
                     FStar_Syntax_Syntax.pos = uu____12148;
                     FStar_Syntax_Syntax.vars = uu____12149;_},uu____12150),FStar_Syntax_Syntax.Tm_arrow
                  uu____12151) ->
                   solve_t' env
                     (let uu___167_12181 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12181.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12181.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12181.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12181.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12181.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12181.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12181.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12181.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12181.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12182,uu____12183) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12194 =
                        let uu____12195 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12195 in
                      if uu____12194
                      then
                        let uu____12196 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_12199 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12199.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12199.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12199.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12199.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12199.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12199.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12199.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12199.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12199.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12200 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12196 uu____12200 t2
                          wl
                      else
                        (let uu____12205 = base_and_refinement env wl t2 in
                         match uu____12205 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12235 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_12238 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12238.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12238.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12238.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12238.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12238.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12238.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12238.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12238.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12238.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12239 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12235
                                    uu____12239 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___170_12254 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12254.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12254.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12257 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12257 in
                                  let guard =
                                    let uu____12265 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____12265
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12271;
                     FStar_Syntax_Syntax.tk = uu____12272;
                     FStar_Syntax_Syntax.pos = uu____12273;
                     FStar_Syntax_Syntax.vars = uu____12274;_},uu____12275),uu____12276)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12301 =
                        let uu____12302 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12302 in
                      if uu____12301
                      then
                        let uu____12303 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_12306 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12306.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12306.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12306.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12306.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12306.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12306.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12306.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12306.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12306.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12307 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12303 uu____12307 t2
                          wl
                      else
                        (let uu____12312 = base_and_refinement env wl t2 in
                         match uu____12312 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12342 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_12345 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12345.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12345.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12345.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12345.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12345.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12345.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12345.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12345.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12345.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12346 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12342
                                    uu____12346 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___170_12361 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12361.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12361.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12364 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12364 in
                                  let guard =
                                    let uu____12372 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____12372
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12378,FStar_Syntax_Syntax.Tm_uvar uu____12379) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12389 = base_and_refinement env wl t1 in
                      match uu____12389 with
                      | (t_base,uu____12400) ->
                          solve_t env
                            (let uu___171_12415 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12415.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12415.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12415.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12415.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12415.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12415.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12415.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12415.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12418,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12419;
                     FStar_Syntax_Syntax.tk = uu____12420;
                     FStar_Syntax_Syntax.pos = uu____12421;
                     FStar_Syntax_Syntax.vars = uu____12422;_},uu____12423))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12447 = base_and_refinement env wl t1 in
                      match uu____12447 with
                      | (t_base,uu____12458) ->
                          solve_t env
                            (let uu___171_12473 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12473.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12473.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12473.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12473.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12473.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12473.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12473.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12473.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12476,uu____12477) ->
                   let t21 =
                     let uu____12485 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12485 in
                   solve_t env
                     (let uu___172_12498 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_12498.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_12498.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_12498.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_12498.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_12498.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_12498.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_12498.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_12498.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_12498.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12499,FStar_Syntax_Syntax.Tm_refine uu____12500) ->
                   let t11 =
                     let uu____12508 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12508 in
                   solve_t env
                     (let uu___173_12521 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12521.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12521.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_12521.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_12521.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12521.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12521.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12521.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12521.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12521.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12524,uu____12525) ->
                   let head1 =
                     let uu____12544 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12544
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12575 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12575
                       FStar_Pervasives_Native.fst in
                   let uu____12603 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12603
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12612 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12612
                      then
                        let guard =
                          let uu____12619 =
                            let uu____12620 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12620 = FStar_Syntax_Util.Equal in
                          if uu____12619
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12623 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_71  ->
                                  FStar_Pervasives_Native.Some _0_71)
                               uu____12623) in
                        let uu____12625 = solve_prob orig guard [] wl in
                        solve env uu____12625
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12628,uu____12629) ->
                   let head1 =
                     let uu____12637 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12637
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12668 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12668
                       FStar_Pervasives_Native.fst in
                   let uu____12696 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12696
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12705 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12705
                      then
                        let guard =
                          let uu____12712 =
                            let uu____12713 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12713 = FStar_Syntax_Util.Equal in
                          if uu____12712
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12716 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_72  ->
                                  FStar_Pervasives_Native.Some _0_72)
                               uu____12716) in
                        let uu____12718 = solve_prob orig guard [] wl in
                        solve env uu____12718
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12721,uu____12722) ->
                   let head1 =
                     let uu____12726 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12726
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12757 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12757
                       FStar_Pervasives_Native.fst in
                   let uu____12785 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12785
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12794 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12794
                      then
                        let guard =
                          let uu____12801 =
                            let uu____12802 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12802 = FStar_Syntax_Util.Equal in
                          if uu____12801
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12805 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_73  ->
                                  FStar_Pervasives_Native.Some _0_73)
                               uu____12805) in
                        let uu____12807 = solve_prob orig guard [] wl in
                        solve env uu____12807
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12810,uu____12811) ->
                   let head1 =
                     let uu____12815 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12815
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12846 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12846
                       FStar_Pervasives_Native.fst in
                   let uu____12874 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12874
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12883 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12883
                      then
                        let guard =
                          let uu____12890 =
                            let uu____12891 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12891 = FStar_Syntax_Util.Equal in
                          if uu____12890
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12894 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_74  ->
                                  FStar_Pervasives_Native.Some _0_74)
                               uu____12894) in
                        let uu____12896 = solve_prob orig guard [] wl in
                        solve env uu____12896
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12899,uu____12900) ->
                   let head1 =
                     let uu____12904 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12904
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____12935 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12935
                       FStar_Pervasives_Native.fst in
                   let uu____12963 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12963
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12972 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12972
                      then
                        let guard =
                          let uu____12979 =
                            let uu____12980 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12980 = FStar_Syntax_Util.Equal in
                          if uu____12979
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12983 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_75  ->
                                  FStar_Pervasives_Native.Some _0_75)
                               uu____12983) in
                        let uu____12985 = solve_prob orig guard [] wl in
                        solve env uu____12985
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12988,uu____12989) ->
                   let head1 =
                     let uu____13002 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13002
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13033 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13033
                       FStar_Pervasives_Native.fst in
                   let uu____13061 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13061
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13070 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13070
                      then
                        let guard =
                          let uu____13077 =
                            let uu____13078 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13078 = FStar_Syntax_Util.Equal in
                          if uu____13077
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13081 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____13081) in
                        let uu____13083 = solve_prob orig guard [] wl in
                        solve env uu____13083
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13086,FStar_Syntax_Syntax.Tm_match uu____13087) ->
                   let head1 =
                     let uu____13106 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13106
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13137 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13137
                       FStar_Pervasives_Native.fst in
                   let uu____13165 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13165
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13174 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13174
                      then
                        let guard =
                          let uu____13181 =
                            let uu____13182 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13182 = FStar_Syntax_Util.Equal in
                          if uu____13181
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13185 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____13185) in
                        let uu____13187 = solve_prob orig guard [] wl in
                        solve env uu____13187
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13190,FStar_Syntax_Syntax.Tm_uinst uu____13191) ->
                   let head1 =
                     let uu____13199 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13199
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13230 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13230
                       FStar_Pervasives_Native.fst in
                   let uu____13258 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13258
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13267 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13267
                      then
                        let guard =
                          let uu____13274 =
                            let uu____13275 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13275 = FStar_Syntax_Util.Equal in
                          if uu____13274
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13278 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____13278) in
                        let uu____13280 = solve_prob orig guard [] wl in
                        solve env uu____13280
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13283,FStar_Syntax_Syntax.Tm_name uu____13284) ->
                   let head1 =
                     let uu____13288 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13288
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13319 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13319
                       FStar_Pervasives_Native.fst in
                   let uu____13347 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13347
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13356 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13356
                      then
                        let guard =
                          let uu____13363 =
                            let uu____13364 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13364 = FStar_Syntax_Util.Equal in
                          if uu____13363
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13367 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____13367) in
                        let uu____13369 = solve_prob orig guard [] wl in
                        solve env uu____13369
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13372,FStar_Syntax_Syntax.Tm_constant uu____13373) ->
                   let head1 =
                     let uu____13377 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13377
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13408 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13408
                       FStar_Pervasives_Native.fst in
                   let uu____13436 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13436
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13445 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13445
                      then
                        let guard =
                          let uu____13452 =
                            let uu____13453 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13453 = FStar_Syntax_Util.Equal in
                          if uu____13452
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13456 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____13456) in
                        let uu____13458 = solve_prob orig guard [] wl in
                        solve env uu____13458
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13461,FStar_Syntax_Syntax.Tm_fvar uu____13462) ->
                   let head1 =
                     let uu____13466 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13466
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13497 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13497
                       FStar_Pervasives_Native.fst in
                   let uu____13525 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13525
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13534 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13534
                      then
                        let guard =
                          let uu____13541 =
                            let uu____13542 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13542 = FStar_Syntax_Util.Equal in
                          if uu____13541
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13545 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____13545) in
                        let uu____13547 = solve_prob orig guard [] wl in
                        solve env uu____13547
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13550,FStar_Syntax_Syntax.Tm_app uu____13551) ->
                   let head1 =
                     let uu____13564 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13564
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____13595 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13595
                       FStar_Pervasives_Native.fst in
                   let uu____13623 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13623
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13632 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13632
                      then
                        let guard =
                          let uu____13639 =
                            let uu____13640 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13640 = FStar_Syntax_Util.Equal in
                          if uu____13639
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13643 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____13643) in
                        let uu____13645 = solve_prob orig guard [] wl in
                        solve env uu____13645
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13649,uu____13650),uu____13651) ->
                   solve_t' env
                     (let uu___174_13680 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_13680.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_13680.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_13680.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_13680.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_13680.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_13680.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_13680.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_13680.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_13680.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13683,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13685,uu____13686)) ->
                   solve_t' env
                     (let uu___175_13715 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13715.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_13715.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13715.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_13715.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13715.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13715.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13715.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13715.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13715.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13716,uu____13717) ->
                   let uu____13725 =
                     let uu____13726 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13727 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13726
                       uu____13727 in
                   failwith uu____13725
               | (FStar_Syntax_Syntax.Tm_meta uu____13728,uu____13729) ->
                   let uu____13734 =
                     let uu____13735 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13736 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13735
                       uu____13736 in
                   failwith uu____13734
               | (FStar_Syntax_Syntax.Tm_delayed uu____13737,uu____13738) ->
                   let uu____13759 =
                     let uu____13760 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13761 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13760
                       uu____13761 in
                   failwith uu____13759
               | (uu____13762,FStar_Syntax_Syntax.Tm_meta uu____13763) ->
                   let uu____13768 =
                     let uu____13769 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13770 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13769
                       uu____13770 in
                   failwith uu____13768
               | (uu____13771,FStar_Syntax_Syntax.Tm_delayed uu____13772) ->
                   let uu____13793 =
                     let uu____13794 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13795 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13794
                       uu____13795 in
                   failwith uu____13793
               | (uu____13796,FStar_Syntax_Syntax.Tm_let uu____13797) ->
                   let uu____13805 =
                     let uu____13806 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13807 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13806
                       uu____13807 in
                   failwith uu____13805
               | uu____13808 -> giveup env "head tag mismatch" orig)))
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
          mk_problem (p_scope orig) orig t1 rel t2
            FStar_Pervasives_Native.None reason in
        let solve_eq c1_comp c2_comp =
          (let uu____13840 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13840
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13848  ->
                  fun uu____13849  ->
                    match (uu____13848, uu____13849) with
                    | ((a1,uu____13859),(a2,uu____13861)) ->
                        let uu____13866 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13866)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____13872 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____13872 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____13892 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13899)::[] -> wp1
              | uu____13912 ->
                  let uu____13918 =
                    let uu____13919 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13919 in
                  failwith uu____13918 in
            let uu____13922 =
              let uu____13928 =
                let uu____13929 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____13929 in
              [uu____13928] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13922;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13930 = lift_c1 () in solve_eq uu____13930 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13934  ->
                       match uu___132_13934 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13935 -> false)) in
             let uu____13936 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13960)::uu____13961,(wp2,uu____13963)::uu____13964)
                   -> (wp1, wp2)
               | uu____14005 ->
                   let uu____14018 =
                     let uu____14019 =
                       let uu____14022 =
                         let uu____14023 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____14024 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14023 uu____14024 in
                       (uu____14022, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____14019 in
                   raise uu____14018 in
             match uu____13936 with
             | (wpc1,wpc2) ->
                 let uu____14041 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____14041
                 then
                   let uu____14044 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____14044 wl
                 else
                   (let uu____14048 =
                      let uu____14052 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14052 in
                    match uu____14048 with
                    | (c2_decl,qualifiers) ->
                        let uu____14064 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14064
                        then
                          let c1_repr =
                            let uu____14067 =
                              let uu____14068 =
                                let uu____14069 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14069 in
                              let uu____14070 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14068 uu____14070 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14067 in
                          let c2_repr =
                            let uu____14072 =
                              let uu____14073 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14074 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14073 uu____14074 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14072 in
                          let prob =
                            let uu____14076 =
                              let uu____14079 =
                                let uu____14080 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14081 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14080
                                  uu____14081 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14079 in
                            FStar_TypeChecker_Common.TProb uu____14076 in
                          let wl1 =
                            let uu____14083 =
                              let uu____14085 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____14085 in
                            solve_prob orig uu____14083 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14092 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14092
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14094 =
                                     let uu____14097 =
                                       let uu____14098 =
                                         let uu____14108 =
                                           let uu____14109 =
                                             let uu____14110 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14110] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14109 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14111 =
                                           let uu____14113 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14114 =
                                             let uu____14116 =
                                               let uu____14117 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14117 in
                                             [uu____14116] in
                                           uu____14113 :: uu____14114 in
                                         (uu____14108, uu____14111) in
                                       FStar_Syntax_Syntax.Tm_app uu____14098 in
                                     FStar_Syntax_Syntax.mk uu____14097 in
                                   uu____14094
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14128 =
                                    let uu____14131 =
                                      let uu____14132 =
                                        let uu____14142 =
                                          let uu____14143 =
                                            let uu____14144 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14144] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14143 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14145 =
                                          let uu____14147 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14148 =
                                            let uu____14150 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14151 =
                                              let uu____14153 =
                                                let uu____14154 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14154 in
                                              [uu____14153] in
                                            uu____14150 :: uu____14151 in
                                          uu____14147 :: uu____14148 in
                                        (uu____14142, uu____14145) in
                                      FStar_Syntax_Syntax.Tm_app uu____14132 in
                                    FStar_Syntax_Syntax.mk uu____14131 in
                                  uu____14128
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14165 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14165 in
                           let wl1 =
                             let uu____14171 =
                               let uu____14173 =
                                 let uu____14176 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____14176 g in
                               FStar_All.pipe_left
                                 (fun _0_85  ->
                                    FStar_Pervasives_Native.Some _0_85)
                                 uu____14173 in
                             solve_prob orig uu____14171 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14186 = FStar_Util.physical_equality c1 c2 in
        if uu____14186
        then
          let uu____14187 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____14187
        else
          ((let uu____14190 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14190
            then
              let uu____14191 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14192 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14191
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14192
            else ());
           (let uu____14194 =
              let uu____14197 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14198 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14197, uu____14198) in
            match uu____14194 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14202),FStar_Syntax_Syntax.Total
                    (t2,uu____14204)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14217 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14217 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14220,FStar_Syntax_Syntax.Total uu____14221) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14233),FStar_Syntax_Syntax.Total
                    (t2,uu____14235)) ->
                     let uu____14248 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14248 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14252),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14254)) ->
                     let uu____14267 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14267 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14271),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14273)) ->
                     let uu____14286 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____14286 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14289,FStar_Syntax_Syntax.Comp uu____14290) ->
                     let uu____14296 =
                       let uu___176_14299 = problem in
                       let uu____14302 =
                         let uu____14303 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14303 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14299.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14302;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14299.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14299.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14299.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14299.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14299.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14299.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14299.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14299.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14296 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14304,FStar_Syntax_Syntax.Comp uu____14305) ->
                     let uu____14311 =
                       let uu___176_14314 = problem in
                       let uu____14317 =
                         let uu____14318 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14318 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14314.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14317;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14314.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14314.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14314.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14314.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14314.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14314.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14314.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14314.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14311 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14319,FStar_Syntax_Syntax.GTotal uu____14320) ->
                     let uu____14326 =
                       let uu___177_14329 = problem in
                       let uu____14332 =
                         let uu____14333 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14333 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14329.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14329.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14329.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14332;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14329.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14329.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14329.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14329.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14329.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14329.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14326 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14334,FStar_Syntax_Syntax.Total uu____14335) ->
                     let uu____14341 =
                       let uu___177_14344 = problem in
                       let uu____14347 =
                         let uu____14348 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14348 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14344.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14344.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14344.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14347;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14344.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14344.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14344.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14344.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14344.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14344.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14341 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14349,FStar_Syntax_Syntax.Comp uu____14350) ->
                     let uu____14351 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14351
                     then
                       let uu____14352 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____14352 wl
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
                           (let uu____14362 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14362
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14364 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14364 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____14366 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14367 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14367) in
                                if uu____14366
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
                                  (let uu____14370 =
                                     let uu____14371 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14372 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14371 uu____14372 in
                                   giveup env uu____14370 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14377 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14397  ->
              match uu____14397 with
              | (uu____14408,uu____14409,u,uu____14411,uu____14412,uu____14413)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14377 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14442 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14442 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14452 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____14464  ->
                match uu____14464 with
                | (u1,u2) ->
                    let uu____14469 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14470 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14469 uu____14470)) in
      FStar_All.pipe_right uu____14452 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14482,[])) -> "{}"
      | uu____14495 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14505 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14505
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14508 =
              FStar_List.map
                (fun uu____14512  ->
                   match uu____14512 with
                   | (uu____14515,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14508 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14519 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14519 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14557 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14557
    then
      let uu____14558 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14559 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14558
        (rel_to_string rel) uu____14559
    else "TOP" in
  let p = new_problem env lhs rel rhs elt loc reason in p
let new_t_prob:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____14579 =
              let uu____14581 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_86  -> FStar_Pervasives_Native.Some _0_86)
                uu____14581 in
            FStar_Syntax_Syntax.new_bv uu____14579 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14587 =
              let uu____14589 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_87  -> FStar_Pervasives_Native.Some _0_87)
                uu____14589 in
            let uu____14591 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14587 uu____14591 in
          ((FStar_TypeChecker_Common.TProb p), x)
let solve_and_commit:
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____14614 = FStar_Options.eager_inference () in
          if uu____14614
          then
            let uu___178_14615 = probs in
            {
              attempting = (uu___178_14615.attempting);
              wl_deferred = (uu___178_14615.wl_deferred);
              ctr = (uu___178_14615.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14615.smt_ok);
              tcenv = (uu___178_14615.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Unionfind.commit tx; FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____14626 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14626
              then
                let uu____14627 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14627
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
          ((let uu____14637 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14637
            then
              let uu____14638 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14638
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14642 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14642
             then
               let uu____14643 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14643
             else ());
            (let f2 =
               let uu____14646 =
                 let uu____14647 = FStar_Syntax_Util.unmeta f1 in
                 uu____14647.FStar_Syntax_Syntax.n in
               match uu____14646 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14651 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_14652 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14652.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14652.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14652.FStar_TypeChecker_Env.implicits)
             })))
let with_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____14667 =
              let uu____14668 =
                let uu____14669 =
                  let uu____14670 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____14670
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14669;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14668 in
            FStar_All.pipe_left
              (fun _0_89  -> FStar_Pervasives_Native.Some _0_89) uu____14667
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____14703 =
        let uu____14704 =
          let uu____14705 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst in
          FStar_All.pipe_right uu____14705
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14704;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      FStar_Pervasives_Native.Some uu____14703
let try_teq:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____14731 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14731
           then
             let uu____14732 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14733 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14732
               uu____14733
           else ());
          (let prob =
             let uu____14736 =
               let uu____14739 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____14739 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14736 in
           let g =
             let uu____14744 =
               let uu____14746 = singleton' env prob smt_ok in
               solve_and_commit env uu____14746
                 (fun uu____14747  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____14744 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14761 = try_teq true env t1 t2 in
        match uu____14761 with
        | FStar_Pervasives_Native.None  ->
            let uu____14763 =
              let uu____14764 =
                let uu____14767 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____14768 = FStar_TypeChecker_Env.get_range env in
                (uu____14767, uu____14768) in
              FStar_Errors.Error uu____14764 in
            raise uu____14763
        | FStar_Pervasives_Native.Some g ->
            ((let uu____14771 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14771
              then
                let uu____14772 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14773 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14774 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14772
                  uu____14773 uu____14774
              else ());
             g)
let try_subtype':
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____14790 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14790
           then
             let uu____14791 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14792 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14791
               uu____14792
           else ());
          (let uu____14794 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14794 with
           | (prob,x) ->
               let g =
                 let uu____14802 =
                   let uu____14804 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14804
                     (fun uu____14805  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14802 in
               ((let uu____14811 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14811
                 then
                   let uu____14812 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14813 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14814 =
                     let uu____14815 = FStar_Util.must g in
                     guard_to_string env uu____14815 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14812 uu____14813 uu____14814
                 else ());
                abstract_guard x g))
let try_subtype:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
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
          let uu____14839 = FStar_TypeChecker_Env.get_range env in
          let uu____14840 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____14839 uu____14840
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14852 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____14852
         then
           let uu____14853 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____14854 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14853
             uu____14854
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____14859 =
             let uu____14862 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____14862 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14859 in
         let uu____14865 =
           let uu____14867 = singleton env prob in
           solve_and_commit env uu____14867
             (fun uu____14868  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____14865)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14887  ->
        match uu____14887 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____14912 =
                 let uu____14913 =
                   let uu____14916 =
                     let uu____14917 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____14918 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14917 uu____14918 in
                   let uu____14919 = FStar_TypeChecker_Env.get_range env in
                   (uu____14916, uu____14919) in
                 FStar_Errors.Error uu____14913 in
               raise uu____14912) in
            let equiv v1 v' =
              let uu____14927 =
                let uu____14930 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____14931 = FStar_Syntax_Subst.compress_univ v' in
                (uu____14930, uu____14931) in
              match uu____14927 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____14939 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14953 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____14953 with
                      | FStar_Syntax_Syntax.U_unif uu____14957 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14968  ->
                                    match uu____14968 with
                                    | (u,v') ->
                                        let uu____14974 = equiv v1 v' in
                                        if uu____14974
                                        then
                                          let uu____14976 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____14976 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____14986 -> [])) in
            let uu____14989 =
              let wl =
                let uu___180_14992 = empty_worklist env in
                {
                  attempting = (uu___180_14992.attempting);
                  wl_deferred = (uu___180_14992.wl_deferred);
                  ctr = (uu___180_14992.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_14992.smt_ok);
                  tcenv = (uu___180_14992.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14999  ->
                      match uu____14999 with
                      | (lb,v1) ->
                          let uu____15004 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____15004 with
                           | USolved wl1 -> ()
                           | uu____15006 -> fail lb v1))) in
            let rec check_ineq uu____15012 =
              match uu____15012 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15019) -> true
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
                      uu____15031,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15033,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15038) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15042,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15047 -> false) in
            let uu____15050 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15056  ->
                      match uu____15056 with
                      | (u,v1) ->
                          let uu____15061 = check_ineq (u, v1) in
                          if uu____15061
                          then true
                          else
                            ((let uu____15064 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15064
                              then
                                let uu____15065 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15066 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15065
                                  uu____15066
                              else ());
                             false))) in
            if uu____15050
            then ()
            else
              ((let uu____15070 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15070
                then
                  ((let uu____15072 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15072);
                   FStar_Unionfind.rollback tx;
                   (let uu____15078 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15078))
                else ());
               (let uu____15084 =
                  let uu____15085 =
                    let uu____15088 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15088) in
                  FStar_Errors.Error uu____15085 in
                raise uu____15084))
let solve_universe_inequalities:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit
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
      let fail uu____15121 =
        match uu____15121 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15131 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15131
       then
         let uu____15132 = wl_to_string wl in
         let uu____15133 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15132 uu____15133
       else ());
      (let g1 =
         let uu____15145 = solve_and_commit env wl fail in
         match uu____15145 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___181_15152 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15152.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15152.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15152.FStar_TypeChecker_Env.implicits)
             }
         | uu____15155 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15158 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15158.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15158.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15158.FStar_TypeChecker_Env.implicits)
        }))
let discharge_guard':
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___183_15184 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15184.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15184.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15184.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15185 =
            let uu____15186 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15186 in
          if uu____15185
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15192 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15192
                   then
                     let uu____15193 = FStar_TypeChecker_Env.get_range env in
                     let uu____15194 =
                       let uu____15195 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15195 in
                     FStar_Errors.diag uu____15193 uu____15194
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Simplify] env vc in
                   match check_trivial vc1 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then FStar_Pervasives_Native.None
                       else
                         ((let uu____15204 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15204
                           then
                             let uu____15205 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15206 =
                               let uu____15207 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15207 in
                             FStar_Errors.diag uu____15205 uu____15206
                           else ());
                          (let vcs =
                             let uu____15213 = FStar_Options.use_tactics () in
                             if uu____15213
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15227  ->
                                   match uu____15227 with
                                   | (env1,goal) ->
                                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                         use_env_range_msg env1 goal)));
                          FStar_Pervasives_Native.Some ret_g))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15238 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____15238 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____15243 =
            let uu____15244 =
              let uu____15247 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15247) in
            FStar_Errors.Error uu____15244 in
          raise uu____15243
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15254 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____15254 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15274 = FStar_Unionfind.find u in
      match uu____15274 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____15283 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15298 = acc in
      match uu____15298 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15344 = hd1 in
               (match uu____15344 with
                | (uu____15351,env,u,tm,k,r) ->
                    let uu____15357 = unresolved u in
                    if uu____15357
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15375 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15375
                        then
                          let uu____15376 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15380 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15381 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15376 uu____15380 uu____15381
                        else ());
                       (let uu____15383 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15387 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15387.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15387.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15387.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15387.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15387.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15387.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15387.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15387.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15387.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15387.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15387.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15387.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15387.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15387.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15387.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15387.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15387.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15387.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15387.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15387.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15387.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15387.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15387.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____15383 with
                        | (uu____15388,uu____15389,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15392 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15392.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15392.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15392.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15395 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____15399  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15395 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_15414 = g in
    let uu____15415 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15414.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15414.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15414.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15415
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15443 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15443 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15450 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15450
      | (reason,uu____15452,uu____15453,e,t,r)::uu____15457 ->
          let uu____15471 =
            let uu____15472 = FStar_Syntax_Print.term_to_string t in
            let uu____15473 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15472 uu____15473 in
          FStar_Errors.err r uu____15471
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15480 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15480.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15480.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15480.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15498 = try_teq false env t1 t2 in
        match uu____15498 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____15501 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____15501 with
             | FStar_Pervasives_Native.Some uu____15505 -> true
             | FStar_Pervasives_Native.None  -> false)