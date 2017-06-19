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
        FStar_TypeChecker_Env.univ_ineqs = uu____23;
        FStar_TypeChecker_Env.implicits = uu____24;_} -> true
    | uu____38 -> false
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
            FStar_TypeChecker_Env.deferred = uu____61;
            FStar_TypeChecker_Env.univ_ineqs = uu____62;
            FStar_TypeChecker_Env.implicits = uu____63;_}
          -> g
      | Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____78 -> failwith "impossible" in
          let uu____79 =
            let uu___134_80 = g1 in
            let uu____81 =
              let uu____82 =
                let uu____83 =
                  let uu____84 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____84] in
                let uu____85 =
                  let uu____92 =
                    let uu____98 =
                      let uu____99 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                      FStar_All.pipe_right uu____99
                        FStar_Syntax_Util.lcomp_of_comp in
                    FStar_All.pipe_right uu____98
                      (fun _0_39  -> FStar_Util.Inl _0_39) in
                  Some uu____92 in
                FStar_Syntax_Util.abs uu____83 f uu____85 in
              FStar_All.pipe_left
                (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
                uu____82 in
            {
              FStar_TypeChecker_Env.guard_f = uu____81;
              FStar_TypeChecker_Env.deferred =
                (uu___134_80.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___134_80.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___134_80.FStar_TypeChecker_Env.implicits)
            } in
          Some uu____79
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___135_122 = g in
          let uu____123 =
            let uu____124 =
              let uu____125 =
                let uu____128 =
                  let uu____129 =
                    let uu____139 =
                      let uu____141 = FStar_Syntax_Syntax.as_arg e in
                      [uu____141] in
                    (f, uu____139) in
                  FStar_Syntax_Syntax.Tm_app uu____129 in
                FStar_Syntax_Syntax.mk uu____128 in
              uu____125
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_41  -> FStar_TypeChecker_Common.NonTrivial _0_41)
              uu____124 in
          {
            FStar_TypeChecker_Env.guard_f = uu____123;
            FStar_TypeChecker_Env.deferred =
              (uu___135_122.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_122.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_122.FStar_TypeChecker_Env.implicits)
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
          let uu___136_165 = g in
          let uu____166 =
            let uu____167 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____167 in
          {
            FStar_TypeChecker_Env.guard_f = uu____166;
            FStar_TypeChecker_Env.deferred =
              (uu___136_165.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___136_165.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___136_165.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____172 -> failwith "impossible"
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
          let uu____185 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____185
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____190 =
      let uu____191 = FStar_Syntax_Util.unmeta t in
      uu____191.FStar_Syntax_Syntax.n in
    match uu____190 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____195 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____231 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____231;
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
                       let uu____283 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____283
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f in
            let uu___137_285 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___137_285.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_285.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_285.FStar_TypeChecker_Env.implicits)
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
               let uu____302 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____302
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
            let uu___138_318 = g in
            let uu____319 =
              let uu____320 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____320 in
            {
              FStar_TypeChecker_Env.guard_f = uu____319;
              FStar_TypeChecker_Env.deferred =
                (uu___138_318.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_318.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_318.FStar_TypeChecker_Env.implicits)
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
        | uu____351 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____366 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____366 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____378 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____378, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____410 = FStar_Syntax_Util.type_u () in
        match uu____410 with
        | (t_type,u) ->
            let uu____415 =
              let uu____418 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____418 t_type in
            (match uu____415 with
             | (tt,uu____420) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____444 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____472 -> false
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
    match projectee with | Success _0 -> true | uu____568 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____584 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____603 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____608 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____613 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___106_631  ->
    match uu___106_631 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____647 =
    let uu____648 = FStar_Syntax_Subst.compress t in
    uu____648.FStar_Syntax_Syntax.n in
  match uu____647 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____665 = FStar_Syntax_Print.uvar_to_string u in
      let uu____666 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____665 uu____666
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____669;
         FStar_Syntax_Syntax.pos = uu____670;
         FStar_Syntax_Syntax.vars = uu____671;_},args)
      ->
      let uu____699 = FStar_Syntax_Print.uvar_to_string u in
      let uu____700 = FStar_Syntax_Print.term_to_string ty in
      let uu____701 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____699 uu____700 uu____701
  | uu____702 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___107_710  ->
      match uu___107_710 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____714 =
            let uu____716 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____717 =
              let uu____719 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____720 =
                let uu____722 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____723 =
                  let uu____725 =
                    let uu____727 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____728 =
                      let uu____730 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____731 =
                        let uu____733 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____734 =
                          let uu____736 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____736] in
                        uu____733 :: uu____734 in
                      uu____730 :: uu____731 in
                    uu____727 :: uu____728 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____725 in
                uu____722 :: uu____723 in
              uu____719 :: uu____720 in
            uu____716 :: uu____717 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____714
      | FStar_TypeChecker_Common.CProb p ->
          let uu____741 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____742 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____741
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____742
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___108_750  ->
      match uu___108_750 with
      | UNIV (u,t) ->
          let x =
            let uu____754 = FStar_Options.hide_uvar_nums () in
            if uu____754
            then "?"
            else
              (let uu____756 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____756 FStar_Util.string_of_int) in
          let uu____757 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____757
      | TERM ((u,uu____759),t) ->
          let x =
            let uu____764 = FStar_Options.hide_uvar_nums () in
            if uu____764
            then "?"
            else
              (let uu____766 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____766 FStar_Util.string_of_int) in
          let uu____767 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____767
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____778 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____778 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____787 =
      let uu____789 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____789
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____787 (FStar_String.concat ", ")
let args_to_string args =
  let uu____809 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____817  ->
            match uu____817 with
            | (x,uu____821) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____809 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____827 =
      let uu____828 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____828 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____827;
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
        let uu___139_844 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___139_844.wl_deferred);
          ctr = (uu___139_844.ctr);
          defer_ok = (uu___139_844.defer_ok);
          smt_ok;
          tcenv = (uu___139_844.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___140_874 = empty_worklist env in
  let uu____875 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____875;
    wl_deferred = (uu___140_874.wl_deferred);
    ctr = (uu___140_874.ctr);
    defer_ok = false;
    smt_ok = (uu___140_874.smt_ok);
    tcenv = (uu___140_874.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___141_890 = wl in
        {
          attempting = (uu___141_890.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___141_890.ctr);
          defer_ok = (uu___141_890.defer_ok);
          smt_ok = (uu___141_890.smt_ok);
          tcenv = (uu___141_890.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___142_904 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___142_904.wl_deferred);
        ctr = (uu___142_904.ctr);
        defer_ok = (uu___142_904.defer_ok);
        smt_ok = (uu___142_904.smt_ok);
        tcenv = (uu___142_904.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____918 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____918
         then
           let uu____919 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____919
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___109_924  ->
    match uu___109_924 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___143_943 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___143_943.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___143_943.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___143_943.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___143_943.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___143_943.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___143_943.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___143_943.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___110_968  ->
    match uu___110_968 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___111_986  ->
      match uu___111_986 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___112_990  ->
    match uu___112_990 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___113_1000  ->
    match uu___113_1000 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___114_1011  ->
    match uu___114_1011 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___115_1022  ->
    match uu___115_1022 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___116_1034  ->
    match uu___116_1034 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___117_1046  ->
    match uu___117_1046 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___118_1056  ->
    match uu___118_1056 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.TProb _0_44) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.CProb _0_45) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1071 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1071 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1087  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1146 = next_pid () in
  let uu____1147 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1146;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1147;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1203 = next_pid () in
  let uu____1204 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1203;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1204;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1253 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1253;
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
        let uu____1313 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1313
        then
          let uu____1314 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1315 = prob_to_string env d in
          let uu____1316 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1314 uu____1315 uu____1316 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1321 -> failwith "impossible" in
           let uu____1322 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1330 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1331 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1330, uu____1331)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1335 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1336 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1335, uu____1336) in
           match uu____1322 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___119_1346  ->
            match uu___119_1346 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1352 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1354),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1369  ->
           match uu___120_1369 with
           | UNIV uu____1371 -> None
           | TERM ((u,uu____1375),t) ->
               let uu____1379 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1379 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1393  ->
           match uu___121_1393 with
           | UNIV (u',t) ->
               let uu____1397 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1397 then Some t else None
           | uu____1400 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1409 =
        let uu____1410 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1410 in
      FStar_Syntax_Subst.compress uu____1409
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1419 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1419
let norm_arg env t = let uu____1441 = sn env (fst t) in (uu____1441, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1460  ->
              match uu____1460 with
              | (x,imp) ->
                  let uu____1467 =
                    let uu___144_1468 = x in
                    let uu____1469 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___144_1468.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___144_1468.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1469
                    } in
                  (uu____1467, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1486 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1486
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1489 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1489
        | uu____1491 -> u2 in
      let uu____1492 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1492
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1608 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1608 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1620;
               FStar_Syntax_Syntax.pos = uu____1621;
               FStar_Syntax_Syntax.vars = uu____1622;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1643 =
                 let uu____1644 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1645 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1644
                   uu____1645 in
               failwith uu____1643)
    | FStar_Syntax_Syntax.Tm_uinst uu____1655 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1682 =
             let uu____1683 = FStar_Syntax_Subst.compress t1' in
             uu____1683.FStar_Syntax_Syntax.n in
           match uu____1682 with
           | FStar_Syntax_Syntax.Tm_refine uu____1695 -> aux true t1'
           | uu____1700 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1712 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1735 =
             let uu____1736 = FStar_Syntax_Subst.compress t1' in
             uu____1736.FStar_Syntax_Syntax.n in
           match uu____1735 with
           | FStar_Syntax_Syntax.Tm_refine uu____1748 -> aux true t1'
           | uu____1753 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1765 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1797 =
             let uu____1798 = FStar_Syntax_Subst.compress t1' in
             uu____1798.FStar_Syntax_Syntax.n in
           match uu____1797 with
           | FStar_Syntax_Syntax.Tm_refine uu____1810 -> aux true t1'
           | uu____1815 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1827 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1839 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1851 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1863 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1875 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1894 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1920 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1940 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1959 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1986 ->
        let uu____1991 =
          let uu____1992 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1993 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1992
            uu____1993 in
        failwith uu____1991
    | FStar_Syntax_Syntax.Tm_ascribed uu____2003 ->
        let uu____2021 =
          let uu____2022 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2023 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2022
            uu____2023 in
        failwith uu____2021
    | FStar_Syntax_Syntax.Tm_delayed uu____2033 ->
        let uu____2054 =
          let uu____2055 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2056 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2055
            uu____2056 in
        failwith uu____2054
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____2066 =
          let uu____2067 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2068 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2067
            uu____2068 in
        failwith uu____2066 in
  let uu____2078 = whnf env t1 in aux false uu____2078
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____2089 =
        let uu____2099 = empty_worklist env in
        base_and_refinement env uu____2099 t in
      FStar_All.pipe_right uu____2089 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2124 = FStar_Syntax_Syntax.null_bv t in
    (uu____2124, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____2148 = base_and_refinement env wl t in
  match uu____2148 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____2209 =
  match uu____2209 with
  | (t_base,refopt) ->
      let uu____2223 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____2223 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___122_2249  ->
      match uu___122_2249 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2253 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2254 =
            let uu____2255 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____2255 in
          let uu____2256 =
            let uu____2257 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____2257 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2253 uu____2254
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2256
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2261 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____2262 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____2263 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2261 uu____2262
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2263
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2268 =
      let uu____2270 =
        let uu____2272 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2282  ->
                  match uu____2282 with | (uu____2286,uu____2287,x) -> x)) in
        FStar_List.append wl.attempting uu____2272 in
      FStar_List.map (wl_prob_to_string wl) uu____2270 in
    FStar_All.pipe_right uu____2268 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2308 =
          let uu____2318 =
            let uu____2319 = FStar_Syntax_Subst.compress k in
            uu____2319.FStar_Syntax_Syntax.n in
          match uu____2318 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2364 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2364)
              else
                (let uu____2378 = FStar_Syntax_Util.abs_formals t in
                 match uu____2378 with
                 | (ys',t1,uu____2399) ->
                     let uu____2412 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2412))
          | uu____2433 ->
              let uu____2434 =
                let uu____2440 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____2440) in
              ((ys, t), uu____2434) in
        match uu____2308 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2499 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2499 c in
               let uu____2501 =
                 let uu____2508 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_46  -> FStar_Util.Inl _0_46) in
                 FStar_All.pipe_right uu____2508 (fun _0_47  -> Some _0_47) in
               FStar_Syntax_Util.abs ys1 t1 uu____2501)
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
            let uu____2564 = p_guard prob in
            match uu____2564 with
            | (uu____2567,uv) ->
                ((let uu____2570 =
                    let uu____2571 = FStar_Syntax_Subst.compress uv in
                    uu____2571.FStar_Syntax_Syntax.n in
                  match uu____2570 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2591 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2591
                        then
                          let uu____2592 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2593 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2594 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2592
                            uu____2593 uu____2594
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2596 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___145_2599 = wl in
                  {
                    attempting = (uu___145_2599.attempting);
                    wl_deferred = (uu___145_2599.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___145_2599.defer_ok);
                    smt_ok = (uu___145_2599.smt_ok);
                    tcenv = (uu___145_2599.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2615 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2615
         then
           let uu____2616 = FStar_Util.string_of_int pid in
           let uu____2617 =
             let uu____2618 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2618 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2616 uu____2617
         else ());
        commit sol;
        (let uu___146_2623 = wl in
         {
           attempting = (uu___146_2623.attempting);
           wl_deferred = (uu___146_2623.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___146_2623.defer_ok);
           smt_ok = (uu___146_2623.smt_ok);
           tcenv = (uu___146_2623.tcenv)
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
            | (uu____2656,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2664 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2664 in
          (let uu____2670 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2670
           then
             let uu____2671 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2672 =
               let uu____2673 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2673 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2671 uu____2672
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2702 =
    let uu____2706 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2706 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2702
    (FStar_Util.for_some
       (fun uu____2723  ->
          match uu____2723 with
          | (uv,uu____2727) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2766 = occurs wl uk t in Prims.op_Negation uu____2766 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2771 =
         let uu____2772 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2773 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2772 uu____2773 in
       Some uu____2771) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2828 = occurs_check env wl uk t in
  match uu____2828 with
  | (occurs_ok,msg) ->
      let uu____2845 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2845, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2913 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2937  ->
            fun uu____2938  ->
              match (uu____2937, uu____2938) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2981 =
                    let uu____2982 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2982 in
                  if uu____2981
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2996 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2996
                     then
                       let uu____3003 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____3003)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2913 with | (isect,uu____3025) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____3082  ->
          fun uu____3083  ->
            match (uu____3082, uu____3083) with
            | ((a,uu____3093),(b,uu____3095)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____3144 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____3150  ->
                match uu____3150 with
                | (b,uu____3154) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____3144 then None else Some (a, (snd hd1))
  | uu____3163 -> None
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
            let uu____3209 = pat_var_opt env seen hd1 in
            (match uu____3209 with
             | None  ->
                 ((let uu____3217 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____3217
                   then
                     let uu____3218 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3218
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3231 =
      let uu____3232 = FStar_Syntax_Subst.compress t in
      uu____3232.FStar_Syntax_Syntax.n in
    match uu____3231 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3235 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3244;
           FStar_Syntax_Syntax.tk = uu____3245;
           FStar_Syntax_Syntax.pos = uu____3246;
           FStar_Syntax_Syntax.vars = uu____3247;_},uu____3248)
        -> true
    | uu____3271 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3335;
         FStar_Syntax_Syntax.pos = uu____3336;
         FStar_Syntax_Syntax.vars = uu____3337;_},args)
      -> (t, uv, k, args)
  | uu____3378 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____3435 = destruct_flex_t t in
  match uu____3435 with
  | (t1,uv,k,args) ->
      let uu____3503 = pat_vars env [] args in
      (match uu____3503 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3559 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3609 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3634 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3639 -> false
let head_match: match_result -> match_result =
  fun uu___123_3643  ->
    match uu___123_3643 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3652 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3667 ->
          let uu____3668 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3668 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3678 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3694 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3700 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3722 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3723 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3724 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3733 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3741 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3758) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3764,uu____3765) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3795) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3810;
             FStar_Syntax_Syntax.index = uu____3811;
             FStar_Syntax_Syntax.sort = t2;_},uu____3813)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3820 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3821 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3822 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3830 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3846 = fv_delta_depth env fv in Some uu____3846
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
            let uu____3868 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3868
            then FullMatch
            else
              (let uu____3870 =
                 let uu____3875 =
                   let uu____3877 = fv_delta_depth env f in Some uu____3877 in
                 let uu____3878 =
                   let uu____3880 = fv_delta_depth env g in Some uu____3880 in
                 (uu____3875, uu____3878) in
               MisMatch uu____3870)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3884),FStar_Syntax_Syntax.Tm_uinst (g,uu____3886)) ->
            let uu____3895 = head_matches env f g in
            FStar_All.pipe_right uu____3895 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3902),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3904)) ->
            let uu____3929 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____3929 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3934),FStar_Syntax_Syntax.Tm_refine (y,uu____3936)) ->
            let uu____3945 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3945 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3947),uu____3948) ->
            let uu____3953 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3953 head_match
        | (uu____3954,FStar_Syntax_Syntax.Tm_refine (x,uu____3956)) ->
            let uu____3961 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3961 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3962,FStar_Syntax_Syntax.Tm_type
           uu____3963) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3964,FStar_Syntax_Syntax.Tm_arrow uu____3965) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3981),FStar_Syntax_Syntax.Tm_app (head',uu____3983))
            ->
            let uu____4012 = head_matches env head1 head' in
            FStar_All.pipe_right uu____4012 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____4014),uu____4015) ->
            let uu____4030 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____4030 head_match
        | (uu____4031,FStar_Syntax_Syntax.Tm_app (head1,uu____4033)) ->
            let uu____4048 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____4048 head_match
        | uu____4049 ->
            let uu____4052 =
              let uu____4057 = delta_depth_of_term env t11 in
              let uu____4059 = delta_depth_of_term env t21 in
              (uu____4057, uu____4059) in
            MisMatch uu____4052
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____4100 = FStar_Syntax_Util.head_and_args t in
    match uu____4100 with
    | (head1,uu____4112) ->
        let uu____4127 =
          let uu____4128 = FStar_Syntax_Util.un_uinst head1 in
          uu____4128.FStar_Syntax_Syntax.n in
        (match uu____4127 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____4133 =
               let uu____4134 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____4134 FStar_Option.isSome in
             if uu____4133
             then
               let uu____4148 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____4148 (fun _0_48  -> Some _0_48)
             else None
         | uu____4151 -> None) in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4219) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4229 =
             let uu____4234 = maybe_inline t11 in
             let uu____4236 = maybe_inline t21 in (uu____4234, uu____4236) in
           match uu____4229 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4257,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4267 =
             let uu____4272 = maybe_inline t11 in
             let uu____4274 = maybe_inline t21 in (uu____4272, uu____4274) in
           match uu____4267 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4299 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____4299 with
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
        let uu____4314 =
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
             let uu____4322 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____4322)) in
        (match uu____4314 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4330 -> fail r
    | uu____4335 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4365 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4397 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4415 = FStar_Syntax_Util.type_u () in
      match uu____4415 with
      | (t,uu____4419) ->
          let uu____4420 = new_uvar r binders t in fst uu____4420
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4431 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____4431 FStar_Pervasives.fst
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
        let uu____4475 = head_matches env t1 t' in
        match uu____4475 with
        | MisMatch uu____4476 -> false
        | uu____4481 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4541,imp),T (t2,uu____4544)) -> (t2, imp)
                     | uu____4561 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4601  ->
                    match uu____4601 with
                    | (t2,uu____4609) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4639 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4639 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4692))::tcs2) ->
                       aux
                         (((let uu___147_4714 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_4714.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_4714.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4724 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___124_4755 =
                 match uu___124_4755 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4818 = decompose1 [] bs1 in
               (rebuild, matches, uu____4818))
      | uu____4846 ->
          let rebuild uu___125_4851 =
            match uu___125_4851 with
            | [] -> t1
            | uu____4853 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___126_4873  ->
    match uu___126_4873 with
    | T (t,uu____4875) -> t
    | uu____4884 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___127_4888  ->
    match uu___127_4888 with
    | T (t,uu____4890) -> FStar_Syntax_Syntax.as_arg t
    | uu____4899 -> failwith "Impossible"
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
              | (uu____4973,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4992 = new_uvar r scope1 k in
                  (match uu____4992 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____5004 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____5019 =
                         let uu____5020 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_49  ->
                              FStar_TypeChecker_Common.TProb _0_49)
                           uu____5020 in
                       ((T (gi_xs, mk_kind)), uu____5019))
              | (uu____5029,uu____5030,C uu____5031) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____5118 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5129;
                         FStar_Syntax_Syntax.pos = uu____5130;
                         FStar_Syntax_Syntax.vars = uu____5131;_})
                        ->
                        let uu____5146 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5146 with
                         | (T (gi_xs,uu____5162),prob) ->
                             let uu____5172 =
                               let uu____5173 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____5173 in
                             (uu____5172, [prob])
                         | uu____5175 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5185;
                         FStar_Syntax_Syntax.pos = uu____5186;
                         FStar_Syntax_Syntax.vars = uu____5187;_})
                        ->
                        let uu____5202 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____5202 with
                         | (T (gi_xs,uu____5218),prob) ->
                             let uu____5228 =
                               let uu____5229 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_51  -> C _0_51)
                                 uu____5229 in
                             (uu____5228, [prob])
                         | uu____5231 -> failwith "impossible")
                    | (uu____5237,uu____5238,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5240;
                         FStar_Syntax_Syntax.pos = uu____5241;
                         FStar_Syntax_Syntax.vars = uu____5242;_})
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
                        let uu____5316 =
                          let uu____5321 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____5321 FStar_List.unzip in
                        (match uu____5316 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5350 =
                                 let uu____5351 =
                                   let uu____5354 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____5354 un_T in
                                 let uu____5355 =
                                   let uu____5361 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____5361
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5351;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5355;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5350 in
                             ((C gi_xs), sub_probs))
                    | uu____5366 ->
                        let uu____5373 = sub_prob scope1 args q in
                        (match uu____5373 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____5118 with
                   | (tc,probs) ->
                       let uu____5391 =
                         match q with
                         | (Some b,uu____5417,uu____5418) ->
                             let uu____5426 =
                               let uu____5430 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____5430 :: args in
                             ((Some b), (b :: scope1), uu____5426)
                         | uu____5448 -> (None, scope1, args) in
                       (match uu____5391 with
                        | (bopt,scope2,args1) ->
                            let uu____5491 = aux scope2 args1 qs2 in
                            (match uu____5491 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5512 =
                                         let uu____5514 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____5514 in
                                       FStar_Syntax_Util.mk_conj_l uu____5512
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____5527 =
                                         let uu____5529 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____5530 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____5529 :: uu____5530 in
                                       FStar_Syntax_Util.mk_conj_l uu____5527 in
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
  let uu___148_5586 = p in
  let uu____5589 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____5590 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___148_5586.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5589;
    FStar_TypeChecker_Common.relation =
      (uu___148_5586.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5590;
    FStar_TypeChecker_Common.element =
      (uu___148_5586.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___148_5586.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___148_5586.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___148_5586.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___148_5586.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___148_5586.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5602 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____5602
            (fun _0_52  -> FStar_TypeChecker_Common.TProb _0_52)
      | FStar_TypeChecker_Common.CProb uu____5607 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5623 = compress_prob wl pr in
        FStar_All.pipe_right uu____5623 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5629 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____5629 with
           | (lh,uu____5642) ->
               let uu____5657 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____5657 with
                | (rh,uu____5670) ->
                    let uu____5685 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5694,FStar_Syntax_Syntax.Tm_uvar uu____5695)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5714,uu____5715)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5726,FStar_Syntax_Syntax.Tm_uvar uu____5727)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5738,uu____5739)
                          ->
                          let uu____5748 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5748 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5788 ->
                                    let rank =
                                      let uu____5795 = is_top_level_prob prob in
                                      if uu____5795
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5797 =
                                      let uu___149_5800 = tp in
                                      let uu____5803 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5800.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___149_5800.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5800.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5803;
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5800.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5800.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5800.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5800.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5800.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5800.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5797)))
                      | (uu____5813,FStar_Syntax_Syntax.Tm_uvar uu____5814)
                          ->
                          let uu____5823 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5823 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5863 ->
                                    let uu____5869 =
                                      let uu___150_5874 = tp in
                                      let uu____5877 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5874.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5877;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5874.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___150_5874.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5874.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5874.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5874.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5874.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5874.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5874.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5869)))
                      | (uu____5893,uu____5894) -> (rigid_rigid, tp) in
                    (match uu____5685 with
                     | (rank,tp1) ->
                         let uu____5905 =
                           FStar_All.pipe_right
                             (let uu___151_5908 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___151_5908.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___151_5908.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___151_5908.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___151_5908.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___151_5908.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___151_5908.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___151_5908.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___151_5908.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___151_5908.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_53  ->
                                FStar_TypeChecker_Common.TProb _0_53) in
                         (rank, uu____5905))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5914 =
            FStar_All.pipe_right
              (let uu___152_5917 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___152_5917.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___152_5917.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___152_5917.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___152_5917.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___152_5917.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___152_5917.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___152_5917.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___152_5917.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___152_5917.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_54  -> FStar_TypeChecker_Common.CProb _0_54) in
          (rigid_rigid, uu____5914)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5950 probs =
      match uu____5950 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5980 = rank wl hd1 in
               (match uu____5980 with
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
    match projectee with | UDeferred _0 -> true | uu____6051 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____6065 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____6079 -> false
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
                        let uu____6117 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____6117 with
                        | (k,uu____6121) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____6125 -> false)))
            | uu____6126 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____6173 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____6173 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____6176 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____6182 =
                     let uu____6183 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____6184 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____6183
                       uu____6184 in
                   UFailed uu____6182)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6200 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6200 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6218 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____6218 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____6221 ->
                let uu____6224 =
                  let uu____6225 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____6226 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6225
                    uu____6226 msg in
                UFailed uu____6224 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6227,uu____6228) ->
              let uu____6229 =
                let uu____6230 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6231 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6230 uu____6231 in
              failwith uu____6229
          | (FStar_Syntax_Syntax.U_unknown ,uu____6232) ->
              let uu____6233 =
                let uu____6234 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6235 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6234 uu____6235 in
              failwith uu____6233
          | (uu____6236,FStar_Syntax_Syntax.U_bvar uu____6237) ->
              let uu____6238 =
                let uu____6239 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6240 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6239 uu____6240 in
              failwith uu____6238
          | (uu____6241,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6242 =
                let uu____6243 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____6244 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6243 uu____6244 in
              failwith uu____6242
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6256 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____6256
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____6266 = occurs_univ v1 u3 in
              if uu____6266
              then
                let uu____6267 =
                  let uu____6268 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6269 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6268 uu____6269 in
                try_umax_components u11 u21 uu____6267
              else
                (let uu____6271 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6271)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____6279 = occurs_univ v1 u3 in
              if uu____6279
              then
                let uu____6280 =
                  let uu____6281 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____6282 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6281 uu____6282 in
                try_umax_components u11 u21 uu____6280
              else
                (let uu____6284 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____6284)
          | (FStar_Syntax_Syntax.U_max uu____6287,uu____6288) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6293 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6293
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6295,FStar_Syntax_Syntax.U_max uu____6296) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____6301 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____6301
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6303,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6304,FStar_Syntax_Syntax.U_name
             uu____6305) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6306) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6307) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6308,FStar_Syntax_Syntax.U_succ
             uu____6309) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6310,FStar_Syntax_Syntax.U_zero
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
  let uu____6380 = bc1 in
  match uu____6380 with
  | (bs1,mk_cod1) ->
      let uu____6405 = bc2 in
      (match uu____6405 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6452 = FStar_Util.first_N n1 bs in
             match uu____6452 with
             | (bs3,rest) ->
                 let uu____6466 = mk_cod rest in (bs3, uu____6466) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____6490 =
               let uu____6494 = mk_cod1 [] in (bs1, uu____6494) in
             let uu____6496 =
               let uu____6500 = mk_cod2 [] in (bs2, uu____6500) in
             (uu____6490, uu____6496)
           else
             if l1 > l2
             then
               (let uu____6527 = curry l2 bs1 mk_cod1 in
                let uu____6537 =
                  let uu____6541 = mk_cod2 [] in (bs2, uu____6541) in
                (uu____6527, uu____6537))
             else
               (let uu____6550 =
                  let uu____6554 = mk_cod1 [] in (bs1, uu____6554) in
                let uu____6556 = curry l1 bs2 mk_cod2 in
                (uu____6550, uu____6556)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6663 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____6663
       then
         let uu____6664 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6664
       else ());
      (let uu____6666 = next_prob probs in
       match uu____6666 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___153_6679 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___153_6679.wl_deferred);
               ctr = (uu___153_6679.ctr);
               defer_ok = (uu___153_6679.defer_ok);
               smt_ok = (uu___153_6679.smt_ok);
               tcenv = (uu___153_6679.tcenv)
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
                  let uu____6686 = solve_flex_rigid_join env tp probs1 in
                  (match uu____6686 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6690 = solve_rigid_flex_meet env tp probs1 in
                     match uu____6690 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6694,uu____6695) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6704 ->
                let uu____6709 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6737  ->
                          match uu____6737 with
                          | (c,uu____6742,uu____6743) -> c < probs.ctr)) in
                (match uu____6709 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6765 =
                            FStar_List.map
                              (fun uu____6771  ->
                                 match uu____6771 with
                                 | (uu____6777,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____6765
                      | uu____6780 ->
                          let uu____6785 =
                            let uu___154_6786 = probs in
                            let uu____6787 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6796  ->
                                      match uu____6796 with
                                      | (uu____6800,uu____6801,y) -> y)) in
                            {
                              attempting = uu____6787;
                              wl_deferred = rest;
                              ctr = (uu___154_6786.ctr);
                              defer_ok = (uu___154_6786.defer_ok);
                              smt_ok = (uu___154_6786.smt_ok);
                              tcenv = (uu___154_6786.tcenv)
                            } in
                          solve env uu____6785))))
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
            let uu____6808 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____6808 with
            | USolved wl1 ->
                let uu____6810 = solve_prob orig None [] wl1 in
                solve env uu____6810
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
                  let uu____6844 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6844 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6847 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6855;
                  FStar_Syntax_Syntax.pos = uu____6856;
                  FStar_Syntax_Syntax.vars = uu____6857;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6860;
                  FStar_Syntax_Syntax.pos = uu____6861;
                  FStar_Syntax_Syntax.vars = uu____6862;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6874,uu____6875) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6880,FStar_Syntax_Syntax.Tm_uinst uu____6881) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6886 -> USolved wl
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
            ((let uu____6894 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6894
              then
                let uu____6895 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6895 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6903 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6903
         then
           let uu____6904 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6904
         else ());
        (let uu____6906 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6906 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6948 = head_matches_delta env () t1 t2 in
               match uu____6948 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6970 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6996 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____7005 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____7006 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____7005, uu____7006)
                          | None  ->
                              let uu____7009 = FStar_Syntax_Subst.compress t1 in
                              let uu____7010 = FStar_Syntax_Subst.compress t2 in
                              (uu____7009, uu____7010) in
                        (match uu____6996 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____7032 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_55  ->
                                    FStar_TypeChecker_Common.TProb _0_55)
                                 uu____7032 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____7055 =
                                    let uu____7061 =
                                      let uu____7064 =
                                        let uu____7067 =
                                          let uu____7068 =
                                            let uu____7073 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____7073) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____7068 in
                                        FStar_Syntax_Syntax.mk uu____7067 in
                                      uu____7064 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____7086 =
                                      let uu____7088 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____7088] in
                                    (uu____7061, uu____7086) in
                                  Some uu____7055
                              | (uu____7097,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7099)) ->
                                  let uu____7104 =
                                    let uu____7108 =
                                      let uu____7110 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____7110] in
                                    (t11, uu____7108) in
                                  Some uu____7104
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7116),uu____7117) ->
                                  let uu____7122 =
                                    let uu____7126 =
                                      let uu____7128 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____7128] in
                                    (t21, uu____7126) in
                                  Some uu____7122
                              | uu____7133 ->
                                  let uu____7136 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____7136 with
                                   | (head1,uu____7151) ->
                                       let uu____7166 =
                                         let uu____7167 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____7167.FStar_Syntax_Syntax.n in
                                       (match uu____7166 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____7174;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____7176;_}
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
                                        | uu____7185 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7194) ->
                  let uu____7207 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___128_7216  ->
                            match uu___128_7216 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____7221 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____7221 with
                                      | (u',uu____7232) ->
                                          let uu____7247 =
                                            let uu____7248 = whnf env u' in
                                            uu____7248.FStar_Syntax_Syntax.n in
                                          (match uu____7247 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7252) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7265 -> false))
                                 | uu____7266 -> false)
                            | uu____7268 -> false)) in
                  (match uu____7207 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7289 tps =
                         match uu____7289 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7316 =
                                    let uu____7321 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____7321 in
                                  (match uu____7316 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7340 -> None) in
                       let uu____7345 =
                         let uu____7350 =
                           let uu____7354 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____7354, []) in
                         make_lower_bound uu____7350 lower_bounds in
                       (match uu____7345 with
                        | None  ->
                            ((let uu____7361 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7361
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
                            ((let uu____7374 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____7374
                              then
                                let wl' =
                                  let uu___155_7376 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___155_7376.wl_deferred);
                                    ctr = (uu___155_7376.ctr);
                                    defer_ok = (uu___155_7376.defer_ok);
                                    smt_ok = (uu___155_7376.smt_ok);
                                    tcenv = (uu___155_7376.tcenv)
                                  } in
                                let uu____7377 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7377
                              else ());
                             (let uu____7379 =
                                solve_t env eq_prob
                                  (let uu___156_7380 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___156_7380.wl_deferred);
                                     ctr = (uu___156_7380.ctr);
                                     defer_ok = (uu___156_7380.defer_ok);
                                     smt_ok = (uu___156_7380.smt_ok);
                                     tcenv = (uu___156_7380.tcenv)
                                   }) in
                              match uu____7379 with
                              | Success uu____7382 ->
                                  let wl1 =
                                    let uu___157_7384 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___157_7384.wl_deferred);
                                      ctr = (uu___157_7384.ctr);
                                      defer_ok = (uu___157_7384.defer_ok);
                                      smt_ok = (uu___157_7384.smt_ok);
                                      tcenv = (uu___157_7384.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____7386 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____7389 -> None))))
              | uu____7390 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7397 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____7397
         then
           let uu____7398 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7398
         else ());
        (let uu____7400 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____7400 with
         | (u,args) ->
             let uu____7427 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____7427 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____7458 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____7458 with
                    | (h1,args1) ->
                        let uu____7486 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____7486 with
                         | (h2,uu____7499) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7518 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____7518
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7533 =
                                          let uu____7535 =
                                            let uu____7536 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____7536 in
                                          [uu____7535] in
                                        Some uu____7533))
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
                                       (let uu____7560 =
                                          let uu____7562 =
                                            let uu____7563 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_57  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_57) uu____7563 in
                                          [uu____7562] in
                                        Some uu____7560))
                                  else None
                              | uu____7571 -> None)) in
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
                             let uu____7637 =
                               let uu____7643 =
                                 let uu____7646 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____7646 in
                               (uu____7643, m1) in
                             Some uu____7637)
                    | (uu____7655,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7657)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7689),uu____7690) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7721 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7755) ->
                       let uu____7768 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___129_7777  ->
                                 match uu___129_7777 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7782 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____7782 with
                                           | (u',uu____7793) ->
                                               let uu____7808 =
                                                 let uu____7809 = whnf env u' in
                                                 uu____7809.FStar_Syntax_Syntax.n in
                                               (match uu____7808 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7813) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7826 -> false))
                                      | uu____7827 -> false)
                                 | uu____7829 -> false)) in
                       (match uu____7768 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7854 tps =
                              match uu____7854 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7895 =
                                         let uu____7902 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7902 in
                                       (match uu____7895 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7937 -> None) in
                            let uu____7944 =
                              let uu____7951 =
                                let uu____7957 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7957, []) in
                              make_upper_bound uu____7951 upper_bounds in
                            (match uu____7944 with
                             | None  ->
                                 ((let uu____7966 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7966
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
                                 ((let uu____7985 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7985
                                   then
                                     let wl' =
                                       let uu___158_7987 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___158_7987.wl_deferred);
                                         ctr = (uu___158_7987.ctr);
                                         defer_ok = (uu___158_7987.defer_ok);
                                         smt_ok = (uu___158_7987.smt_ok);
                                         tcenv = (uu___158_7987.tcenv)
                                       } in
                                     let uu____7988 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7988
                                   else ());
                                  (let uu____7990 =
                                     solve_t env eq_prob
                                       (let uu___159_7991 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___159_7991.wl_deferred);
                                          ctr = (uu___159_7991.ctr);
                                          defer_ok = (uu___159_7991.defer_ok);
                                          smt_ok = (uu___159_7991.smt_ok);
                                          tcenv = (uu___159_7991.tcenv)
                                        }) in
                                   match uu____7990 with
                                   | Success uu____7993 ->
                                       let wl1 =
                                         let uu___160_7995 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___160_7995.wl_deferred);
                                           ctr = (uu___160_7995.ctr);
                                           defer_ok =
                                             (uu___160_7995.defer_ok);
                                           smt_ok = (uu___160_7995.smt_ok);
                                           tcenv = (uu___160_7995.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7997 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____8000 -> None))))
                   | uu____8001 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____8066 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____8066
                      then
                        let uu____8067 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____8067
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___161_8099 = hd1 in
                      let uu____8100 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_8099.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_8099.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8100
                      } in
                    let hd21 =
                      let uu___162_8104 = hd2 in
                      let uu____8105 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_8104.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_8104.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8105
                      } in
                    let prob =
                      let uu____8109 =
                        let uu____8112 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____8112 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_58  -> FStar_TypeChecker_Common.TProb _0_58)
                        uu____8109 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____8120 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____8120 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____8123 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____8123 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____8141 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____8144 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____8141 uu____8144 in
                         ((let uu____8150 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____8150
                           then
                             let uu____8151 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____8152 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____8151 uu____8152
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____8167 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____8173 = aux scope env [] bs1 bs2 in
              match uu____8173 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____8189 = compress_tprob wl problem in
        solve_t' env uu____8189 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____8222 = head_matches_delta env1 wl1 t1 t2 in
          match uu____8222 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8239,uu____8240) ->
                   let may_relate head3 =
                     let uu____8255 =
                       let uu____8256 = FStar_Syntax_Util.un_uinst head3 in
                       uu____8256.FStar_Syntax_Syntax.n in
                     match uu____8255 with
                     | FStar_Syntax_Syntax.Tm_name uu____8259 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8260 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8277 -> false in
                   let uu____8278 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____8278
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
                                let uu____8295 =
                                  let uu____8296 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8296 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____8295 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____8298 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____8298
                   else
                     (let uu____8300 =
                        let uu____8301 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____8302 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8301 uu____8302 in
                      giveup env1 uu____8300 orig)
               | (uu____8303,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___163_8311 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_8311.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_8311.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_8311.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_8311.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_8311.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_8311.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_8311.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_8311.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8312,None ) ->
                   ((let uu____8319 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8319
                     then
                       let uu____8320 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____8321 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____8322 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____8323 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8320
                         uu____8321 uu____8322 uu____8323
                     else ());
                    (let uu____8325 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____8325 with
                     | (head11,args1) ->
                         let uu____8351 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____8351 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8396 =
                                  let uu____8397 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____8398 = args_to_string args1 in
                                  let uu____8399 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____8400 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8397 uu____8398 uu____8399
                                    uu____8400 in
                                giveup env1 uu____8396 orig
                              else
                                (let uu____8402 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8407 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____8407 = FStar_Syntax_Util.Equal) in
                                 if uu____8402
                                 then
                                   let uu____8408 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____8408 with
                                   | USolved wl2 ->
                                       let uu____8410 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____8410
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8414 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____8414 with
                                    | (base1,refinement1) ->
                                        let uu____8440 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____8440 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8494 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____8494 with
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
                                                           (fun uu____8504 
                                                              ->
                                                              fun uu____8505 
                                                                ->
                                                                match 
                                                                  (uu____8504,
                                                                    uu____8505)
                                                                with
                                                                | ((a,uu____8515),
                                                                   (a',uu____8517))
                                                                    ->
                                                                    let uu____8522
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
                                                                    uu____8522)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____8528 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8528 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8532 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___164_8565 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___164_8565.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____8585 = p in
          match uu____8585 with
          | (((u,k),xs,c),ps,(h,uu____8596,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8645 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____8645 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8659 = h gs_xs in
                     let uu____8660 =
                       let uu____8667 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_60  -> FStar_Util.Inl _0_60) in
                       FStar_All.pipe_right uu____8667
                         (fun _0_61  -> Some _0_61) in
                     FStar_Syntax_Util.abs xs1 uu____8659 uu____8660 in
                   ((let uu____8698 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____8698
                     then
                       let uu____8699 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____8700 = FStar_Syntax_Print.comp_to_string c in
                       let uu____8701 = FStar_Syntax_Print.term_to_string im in
                       let uu____8702 = FStar_Syntax_Print.tag_of_term im in
                       let uu____8703 =
                         let uu____8704 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____8704
                           (FStar_String.concat ", ") in
                       let uu____8707 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8699 uu____8700 uu____8701 uu____8702
                         uu____8703 uu____8707
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___130_8725 =
          match uu___130_8725 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____8754 = p in
          match uu____8754 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____8812 = FStar_List.nth ps i in
              (match uu____8812 with
               | (pi,uu____8815) ->
                   let uu____8820 = FStar_List.nth xs i in
                   (match uu____8820 with
                    | (xi,uu____8827) ->
                        let rec gs k =
                          let uu____8836 = FStar_Syntax_Util.arrow_formals k in
                          match uu____8836 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8888)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8896 = new_uvar r xs k_a in
                                    (match uu____8896 with
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
                                         let uu____8915 = aux subst2 tl1 in
                                         (match uu____8915 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8930 =
                                                let uu____8932 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8932 :: gi_xs' in
                                              let uu____8933 =
                                                let uu____8935 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8935 :: gi_ps' in
                                              (uu____8930, uu____8933))) in
                              aux [] bs in
                        let uu____8938 =
                          let uu____8939 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8939 in
                        if uu____8938
                        then None
                        else
                          (let uu____8942 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8942 with
                           | (g_xs,uu____8949) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8956 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8961 =
                                   let uu____8968 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_62  -> FStar_Util.Inl _0_62) in
                                   FStar_All.pipe_right uu____8968
                                     (fun _0_63  -> Some _0_63) in
                                 FStar_Syntax_Util.abs xs uu____8956
                                   uu____8961 in
                               let sub1 =
                                 let uu____8999 =
                                   let uu____9002 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____9009 =
                                     let uu____9012 =
                                       FStar_List.map
                                         (fun uu____9018  ->
                                            match uu____9018 with
                                            | (uu____9023,uu____9024,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____9012 in
                                   mk_problem (p_scope orig) orig uu____9002
                                     (p_rel orig) uu____9009 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____8999 in
                               ((let uu____9034 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____9034
                                 then
                                   let uu____9035 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____9036 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____9035 uu____9036
                                 else ());
                                (let wl2 =
                                   let uu____9039 =
                                     let uu____9041 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____9041 in
                                   solve_prob orig uu____9039
                                     [TERM (u, proj)] wl1 in
                                 let uu____9046 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_65  -> Some _0_65) uu____9046))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____9070 = lhs in
          match uu____9070 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____9093 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____9093 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____9119 =
                        let uu____9145 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____9145) in
                      Some uu____9119
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____9228 =
                           let uu____9232 =
                             let uu____9233 = FStar_Syntax_Subst.compress k in
                             uu____9233.FStar_Syntax_Syntax.n in
                           (uu____9232, args) in
                         match uu____9228 with
                         | (uu____9240,[]) ->
                             let uu____9242 =
                               let uu____9248 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____9248) in
                             Some uu____9242
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9259,uu____9260) ->
                             let uu____9271 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9271 with
                              | (uv1,uv_args) ->
                                  let uu____9300 =
                                    let uu____9301 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9301.FStar_Syntax_Syntax.n in
                                  (match uu____9300 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9308) ->
                                       let uu____9321 =
                                         pat_vars env [] uv_args in
                                       (match uu____9321 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9335  ->
                                                      let uu____9336 =
                                                        let uu____9337 =
                                                          let uu____9338 =
                                                            let uu____9341 =
                                                              let uu____9342
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9342
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9341 in
                                                          fst uu____9338 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9337 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9336)) in
                                            let c1 =
                                              let uu____9348 =
                                                let uu____9349 =
                                                  let uu____9352 =
                                                    let uu____9353 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9353
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9352 in
                                                fst uu____9349 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9348 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9362 =
                                                let uu____9369 =
                                                  let uu____9375 =
                                                    let uu____9376 =
                                                      let uu____9379 =
                                                        let uu____9380 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9380
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9379 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9376 in
                                                  FStar_Util.Inl uu____9375 in
                                                Some uu____9369 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9362 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9400 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9403,uu____9404)
                             ->
                             let uu____9416 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____9416 with
                              | (uv1,uv_args) ->
                                  let uu____9445 =
                                    let uu____9446 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____9446.FStar_Syntax_Syntax.n in
                                  (match uu____9445 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9453) ->
                                       let uu____9466 =
                                         pat_vars env [] uv_args in
                                       (match uu____9466 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9480  ->
                                                      let uu____9481 =
                                                        let uu____9482 =
                                                          let uu____9483 =
                                                            let uu____9486 =
                                                              let uu____9487
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____9487
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9486 in
                                                          fst uu____9483 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9482 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9481)) in
                                            let c1 =
                                              let uu____9493 =
                                                let uu____9494 =
                                                  let uu____9497 =
                                                    let uu____9498 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____9498
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9497 in
                                                fst uu____9494 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9493 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____9507 =
                                                let uu____9514 =
                                                  let uu____9520 =
                                                    let uu____9521 =
                                                      let uu____9524 =
                                                        let uu____9525 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____9525
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9524 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9521 in
                                                  FStar_Util.Inl uu____9520 in
                                                Some uu____9514 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9507 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9545 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9550)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____9582 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____9582
                                 (fun _0_66  -> Some _0_66)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9606 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____9606 with
                                  | (args1,rest) ->
                                      let uu____9624 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____9624 with
                                       | (xs2,c2) ->
                                           let uu____9632 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____9632
                                             (fun uu____9643  ->
                                                match uu____9643 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9665 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____9665 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____9713 =
                                        let uu____9716 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9716 in
                                      FStar_All.pipe_right uu____9713
                                        (fun _0_67  -> Some _0_67))
                         | uu____9724 ->
                             let uu____9728 =
                               let uu____9729 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____9730 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____9731 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9729 uu____9730 uu____9731 in
                             failwith uu____9728 in
                       let uu____9735 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____9735
                         (fun uu____9763  ->
                            match uu____9763 with
                            | (xs1,c1) ->
                                let uu____9791 =
                                  let uu____9814 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9814) in
                                Some uu____9791)) in
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
                     let uu____9886 = imitate orig env wl1 st in
                     match uu____9886 with
                     | Failed uu____9891 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9897 = project orig env wl1 i st in
                      match uu____9897 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9904) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____9918 = FStar_Syntax_Util.head_and_args t21 in
                match uu____9918 with
                | (hd1,uu____9929) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9944 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9952 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9953 -> true
                     | uu____9968 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____9971 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____9971
                         then true
                         else
                           ((let uu____9974 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____9974
                             then
                               let uu____9975 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9975
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9983 =
                    let uu____9986 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____9986 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____9983 FStar_Syntax_Free.names in
                let uu____10017 = FStar_Util.set_is_empty fvs_hd in
                if uu____10017
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____10026 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____10026 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____10034 =
                            let uu____10035 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____10035 in
                          giveup_or_defer1 orig uu____10034
                        else
                          (let uu____10037 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____10037
                           then
                             let uu____10038 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____10038
                              then
                                let uu____10039 = subterms args_lhs in
                                imitate' orig env wl1 uu____10039
                              else
                                ((let uu____10043 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____10043
                                  then
                                    let uu____10044 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____10045 = names_to_string fvs1 in
                                    let uu____10046 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____10044 uu____10045 uu____10046
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____10051 ->
                                        let uu____10052 = sn_binders env vars in
                                        u_abs k_uv uu____10052 t21 in
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
                               (let uu____10061 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____10061
                                then
                                  ((let uu____10063 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____10063
                                    then
                                      let uu____10064 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____10065 = names_to_string fvs1 in
                                      let uu____10066 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____10064 uu____10065 uu____10066
                                    else ());
                                   (let uu____10068 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____10068 (- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | None  when patterns_only -> giveup env "not a pattern" orig
               | None  ->
                   if wl1.defer_ok
                   then solve env (defer "not a pattern" orig wl1)
                   else
                     (let uu____10082 =
                        let uu____10083 = FStar_Syntax_Free.names t1 in
                        check_head uu____10083 t2 in
                      if uu____10082
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____10087 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____10087
                          then
                            let uu____10088 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____10088
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____10091 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____10091 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____10136 =
               match uu____10136 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____10167 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____10167 with
                    | (all_formals,uu____10178) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10270  ->
                                        match uu____10270 with
                                        | (x,imp) ->
                                            let uu____10277 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____10277, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____10285 = FStar_Syntax_Util.type_u () in
                                match uu____10285 with
                                | (t1,uu____10289) ->
                                    let uu____10290 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____10290 in
                              let uu____10293 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____10293 with
                               | (t',tm_u1) ->
                                   let uu____10300 = destruct_flex_t t' in
                                   (match uu____10300 with
                                    | (uu____10320,u1,k11,uu____10323) ->
                                        let sol =
                                          let uu____10351 =
                                            let uu____10356 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____10356) in
                                          TERM uu____10351 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10416 = pat_var_opt env pat_args hd1 in
                              (match uu____10416 with
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
                                              (fun uu____10445  ->
                                                 match uu____10445 with
                                                 | (x,uu____10449) ->
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
                                      let uu____10455 =
                                        let uu____10456 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____10456 in
                                      if uu____10455
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10460 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10460 formals1
                                           tl1)))
                          | uu____10466 -> failwith "Impossible" in
                        let uu____10477 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____10477 all_formals args) in
             let solve_both_pats wl1 uu____10517 uu____10518 r =
               match (uu____10517, uu____10518) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10632 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____10632
                   then
                     let uu____10633 = solve_prob orig None [] wl1 in
                     solve env uu____10633
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____10648 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____10648
                       then
                         let uu____10649 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____10650 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____10651 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____10652 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____10653 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10649 uu____10650 uu____10651 uu____10652
                           uu____10653
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____10701 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____10701 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10714 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____10714 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10746 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10746 in
                                  let uu____10749 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____10749 k3)
                           else
                             (let uu____10752 =
                                let uu____10753 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____10754 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____10755 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10753 uu____10754 uu____10755 in
                              failwith uu____10752) in
                       let uu____10756 =
                         let uu____10762 =
                           let uu____10770 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____10770 in
                         match uu____10762 with
                         | (bs,k1') ->
                             let uu____10788 =
                               let uu____10796 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____10796 in
                             (match uu____10788 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____10817 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_68  ->
                                         FStar_TypeChecker_Common.TProb _0_68)
                                      uu____10817 in
                                  let uu____10822 =
                                    let uu____10825 =
                                      let uu____10826 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____10826.FStar_Syntax_Syntax.n in
                                    let uu____10829 =
                                      let uu____10830 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____10830.FStar_Syntax_Syntax.n in
                                    (uu____10825, uu____10829) in
                                  (match uu____10822 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10838,uu____10839) ->
                                       (k1', [sub_prob])
                                   | (uu____10843,FStar_Syntax_Syntax.Tm_type
                                      uu____10844) -> (k2', [sub_prob])
                                   | uu____10848 ->
                                       let uu____10851 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____10851 with
                                        | (t,uu____10860) ->
                                            let uu____10861 = new_uvar r zs t in
                                            (match uu____10861 with
                                             | (k_zs,uu____10870) ->
                                                 let kprob =
                                                   let uu____10872 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_69  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_69) uu____10872 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____10756 with
                       | (k_u',sub_probs) ->
                           let uu____10886 =
                             let uu____10894 =
                               let uu____10895 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10895 in
                             let uu____10900 =
                               let uu____10903 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____10903 in
                             let uu____10906 =
                               let uu____10909 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____10909 in
                             (uu____10894, uu____10900, uu____10906) in
                           (match uu____10886 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____10928 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____10928 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____10940 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____10940
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____10944 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____10944 with
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
             let solve_one_pat uu____10976 uu____10977 =
               match (uu____10976, uu____10977) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____11041 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____11041
                     then
                       let uu____11042 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11043 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____11042 uu____11043
                     else ());
                    (let uu____11045 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____11045
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____11052  ->
                              fun uu____11053  ->
                                match (uu____11052, uu____11053) with
                                | ((a,uu____11063),(t21,uu____11065)) ->
                                    let uu____11070 =
                                      let uu____11073 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____11073
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____11070
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70))
                           xs args2 in
                       let guard =
                         let uu____11077 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____11077 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____11087 = occurs_check env wl (u1, k1) t21 in
                        match uu____11087 with
                        | (occurs_ok,uu____11092) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____11097 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____11097
                            then
                              let sol =
                                let uu____11099 =
                                  let uu____11104 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____11104) in
                                TERM uu____11099 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____11109 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____11109
                               then
                                 let uu____11110 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____11110 with
                                 | (sol,(uu____11120,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____11130 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____11130
                                       then
                                         let uu____11131 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____11131
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____11136 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____11138 = lhs in
             match uu____11138 with
             | (t1,u1,k1,args1) ->
                 let uu____11143 = rhs in
                 (match uu____11143 with
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
                       | uu____11169 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11175 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____11175 with
                              | (sol,uu____11182) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____11185 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____11185
                                    then
                                      let uu____11186 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11186
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11191 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____11193 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____11193
        then
          let uu____11194 = solve_prob orig None [] wl in
          solve env uu____11194
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____11198 = FStar_Util.physical_equality t1 t2 in
           if uu____11198
           then
             let uu____11199 = solve_prob orig None [] wl in
             solve env uu____11199
           else
             ((let uu____11202 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____11202
               then
                 let uu____11203 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____11203
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11206,uu____11207) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11208,FStar_Syntax_Syntax.Tm_bvar uu____11209) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___131_11249 =
                     match uu___131_11249 with
                     | [] -> c
                     | bs ->
                         let uu____11263 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____11263 in
                   let uu____11273 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____11273 with
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
                                   let uu____11359 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____11359
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____11361 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.CProb _0_71)
                                   uu____11361))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___132_11438 =
                     match uu___132_11438 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____11473 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____11473 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11556 =
                                   let uu____11559 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____11560 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____11559
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11560 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_72  ->
                                      FStar_TypeChecker_Common.TProb _0_72)
                                   uu____11556))
               | (FStar_Syntax_Syntax.Tm_abs uu____11563,uu____11564) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11587 -> true
                     | uu____11602 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11630 =
                     let uu____11641 = maybe_eta t1 in
                     let uu____11646 = maybe_eta t2 in
                     (uu____11641, uu____11646) in
                   (match uu____11630 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11677 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11677.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11677.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11677.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11677.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11677.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11677.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11677.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11677.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11696 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11696
                        then
                          let uu____11697 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11697 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11718 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11718
                        then
                          let uu____11719 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11719 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11724 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11735,FStar_Syntax_Syntax.Tm_abs uu____11736) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11759 -> true
                     | uu____11774 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____11802 =
                     let uu____11813 = maybe_eta t1 in
                     let uu____11818 = maybe_eta t2 in
                     (uu____11813, uu____11818) in
                   (match uu____11802 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___165_11849 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___165_11849.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___165_11849.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___165_11849.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___165_11849.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___165_11849.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___165_11849.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___165_11849.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___165_11849.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11868 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11868
                        then
                          let uu____11869 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11869 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11890 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____11890
                        then
                          let uu____11891 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____11891 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11896 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11907,FStar_Syntax_Syntax.Tm_refine uu____11908) ->
                   let uu____11917 = as_refinement env wl t1 in
                   (match uu____11917 with
                    | (x1,phi1) ->
                        let uu____11922 = as_refinement env wl t2 in
                        (match uu____11922 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11928 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_73  ->
                                    FStar_TypeChecker_Common.TProb _0_73)
                                 uu____11928 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11961 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____11961
                                 (guard_on_element wl problem x11) in
                             let fallback uu____11965 =
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
                                 let uu____11971 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11971 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11978 =
                                   let uu____11981 =
                                     let uu____11982 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____11982 :: (p_scope orig) in
                                   mk_problem uu____11981 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_74  ->
                                      FStar_TypeChecker_Common.TProb _0_74)
                                   uu____11978 in
                               let uu____11985 =
                                 solve env1
                                   (let uu___166_11986 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___166_11986.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___166_11986.smt_ok);
                                      tcenv = (uu___166_11986.tcenv)
                                    }) in
                               (match uu____11985 with
                                | Failed uu____11990 -> fallback ()
                                | Success uu____11993 ->
                                    let guard =
                                      let uu____11997 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____12000 =
                                        let uu____12001 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____12001
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____11997
                                        uu____12000 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___167_12008 = wl1 in
                                      {
                                        attempting =
                                          (uu___167_12008.attempting);
                                        wl_deferred =
                                          (uu___167_12008.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___167_12008.defer_ok);
                                        smt_ok = (uu___167_12008.smt_ok);
                                        tcenv = (uu___167_12008.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12010,FStar_Syntax_Syntax.Tm_uvar uu____12011) ->
                   let uu____12028 = destruct_flex_t t1 in
                   let uu____12029 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12028 uu____12029
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12030;
                     FStar_Syntax_Syntax.tk = uu____12031;
                     FStar_Syntax_Syntax.pos = uu____12032;
                     FStar_Syntax_Syntax.vars = uu____12033;_},uu____12034),FStar_Syntax_Syntax.Tm_uvar
                  uu____12035) ->
                   let uu____12066 = destruct_flex_t t1 in
                   let uu____12067 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12066 uu____12067
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12068,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12069;
                     FStar_Syntax_Syntax.tk = uu____12070;
                     FStar_Syntax_Syntax.pos = uu____12071;
                     FStar_Syntax_Syntax.vars = uu____12072;_},uu____12073))
                   ->
                   let uu____12104 = destruct_flex_t t1 in
                   let uu____12105 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12104 uu____12105
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12106;
                     FStar_Syntax_Syntax.tk = uu____12107;
                     FStar_Syntax_Syntax.pos = uu____12108;
                     FStar_Syntax_Syntax.vars = uu____12109;_},uu____12110),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12111;
                     FStar_Syntax_Syntax.tk = uu____12112;
                     FStar_Syntax_Syntax.pos = uu____12113;
                     FStar_Syntax_Syntax.vars = uu____12114;_},uu____12115))
                   ->
                   let uu____12160 = destruct_flex_t t1 in
                   let uu____12161 = destruct_flex_t t2 in
                   flex_flex1 orig uu____12160 uu____12161
               | (FStar_Syntax_Syntax.Tm_uvar uu____12162,uu____12163) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12172 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12172 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12176;
                     FStar_Syntax_Syntax.tk = uu____12177;
                     FStar_Syntax_Syntax.pos = uu____12178;
                     FStar_Syntax_Syntax.vars = uu____12179;_},uu____12180),uu____12181)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12204 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____12204 t2 wl
               | (uu____12208,FStar_Syntax_Syntax.Tm_uvar uu____12209) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12218,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12219;
                     FStar_Syntax_Syntax.tk = uu____12220;
                     FStar_Syntax_Syntax.pos = uu____12221;
                     FStar_Syntax_Syntax.vars = uu____12222;_},uu____12223))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12246,FStar_Syntax_Syntax.Tm_type uu____12247) ->
                   solve_t' env
                     (let uu___168_12256 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12256.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12256.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12256.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12256.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12256.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12256.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12256.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12256.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12256.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12257;
                     FStar_Syntax_Syntax.tk = uu____12258;
                     FStar_Syntax_Syntax.pos = uu____12259;
                     FStar_Syntax_Syntax.vars = uu____12260;_},uu____12261),FStar_Syntax_Syntax.Tm_type
                  uu____12262) ->
                   solve_t' env
                     (let uu___168_12285 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12285.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12285.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12285.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12285.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12285.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12285.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12285.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12285.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12285.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12286,FStar_Syntax_Syntax.Tm_arrow uu____12287) ->
                   solve_t' env
                     (let uu___168_12303 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12303.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12303.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12303.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12303.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12303.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12303.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12303.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12303.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12303.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12304;
                     FStar_Syntax_Syntax.tk = uu____12305;
                     FStar_Syntax_Syntax.pos = uu____12306;
                     FStar_Syntax_Syntax.vars = uu____12307;_},uu____12308),FStar_Syntax_Syntax.Tm_arrow
                  uu____12309) ->
                   solve_t' env
                     (let uu___168_12339 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___168_12339.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___168_12339.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___168_12339.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___168_12339.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___168_12339.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___168_12339.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___168_12339.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___168_12339.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___168_12339.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12340,uu____12341) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12352 =
                        let uu____12353 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12353 in
                      if uu____12352
                      then
                        let uu____12354 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___169_12357 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12357.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12357.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12357.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12357.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12357.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12357.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12357.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12357.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12357.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12358 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12354 uu____12358 t2
                          wl
                      else
                        (let uu____12363 = base_and_refinement env wl t2 in
                         match uu____12363 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12393 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___170_12396 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12396.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12396.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12396.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12396.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12396.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12396.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12396.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12396.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12396.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12397 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12393
                                    uu____12397 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12412 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12412.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12412.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12415 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____12415 in
                                  let guard =
                                    let uu____12423 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12423
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12429;
                     FStar_Syntax_Syntax.tk = uu____12430;
                     FStar_Syntax_Syntax.pos = uu____12431;
                     FStar_Syntax_Syntax.vars = uu____12432;_},uu____12433),uu____12434)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____12459 =
                        let uu____12460 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____12460 in
                      if uu____12459
                      then
                        let uu____12461 =
                          FStar_All.pipe_left
                            (fun _0_78  ->
                               FStar_TypeChecker_Common.TProb _0_78)
                            (let uu___169_12464 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_12464.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_12464.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_12464.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_12464.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_12464.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_12464.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_12464.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_12464.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_12464.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____12465 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____12461 uu____12465 t2
                          wl
                      else
                        (let uu____12470 = base_and_refinement env wl t2 in
                         match uu____12470 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12500 =
                                    FStar_All.pipe_left
                                      (fun _0_79  ->
                                         FStar_TypeChecker_Common.TProb _0_79)
                                      (let uu___170_12503 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___170_12503.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___170_12503.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___170_12503.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___170_12503.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___170_12503.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___170_12503.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___170_12503.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___170_12503.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___170_12503.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____12504 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____12500
                                    uu____12504 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___171_12519 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___171_12519.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___171_12519.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____12522 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_80  ->
                                         FStar_TypeChecker_Common.TProb _0_80)
                                      uu____12522 in
                                  let guard =
                                    let uu____12530 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____12530
                                      impl in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12536,FStar_Syntax_Syntax.Tm_uvar uu____12537) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12547 = base_and_refinement env wl t1 in
                      match uu____12547 with
                      | (t_base,uu____12558) ->
                          solve_t env
                            (let uu___172_12573 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12573.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12573.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12573.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12573.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12573.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12573.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12573.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12573.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12576,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12577;
                     FStar_Syntax_Syntax.tk = uu____12578;
                     FStar_Syntax_Syntax.pos = uu____12579;
                     FStar_Syntax_Syntax.vars = uu____12580;_},uu____12581))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12605 = base_and_refinement env wl t1 in
                      match uu____12605 with
                      | (t_base,uu____12616) ->
                          solve_t env
                            (let uu___172_12631 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___172_12631.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___172_12631.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___172_12631.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___172_12631.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___172_12631.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___172_12631.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___172_12631.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___172_12631.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12634,uu____12635) ->
                   let t21 =
                     let uu____12643 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____12643 in
                   solve_t env
                     (let uu___173_12656 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12656.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_12656.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12656.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_12656.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12656.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12656.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12656.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12656.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12656.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12657,FStar_Syntax_Syntax.Tm_refine uu____12658) ->
                   let t11 =
                     let uu____12666 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____12666 in
                   solve_t env
                     (let uu___174_12679 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12679.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12679.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_12679.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_12679.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12679.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12679.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12679.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12679.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12679.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12682,uu____12683) ->
                   let head1 =
                     let uu____12702 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12702 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12733 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12733 FStar_Pervasives.fst in
                   let uu____12761 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12761
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12770 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12770
                      then
                        let guard =
                          let uu____12777 =
                            let uu____12778 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12778 = FStar_Syntax_Util.Equal in
                          if uu____12777
                          then None
                          else
                            (let uu____12781 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____12781) in
                        let uu____12783 = solve_prob orig guard [] wl in
                        solve env uu____12783
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12786,uu____12787) ->
                   let head1 =
                     let uu____12795 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12795 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12826 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12826 FStar_Pervasives.fst in
                   let uu____12854 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12854
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12863 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12863
                      then
                        let guard =
                          let uu____12870 =
                            let uu____12871 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12871 = FStar_Syntax_Util.Equal in
                          if uu____12870
                          then None
                          else
                            (let uu____12874 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____12874) in
                        let uu____12876 = solve_prob orig guard [] wl in
                        solve env uu____12876
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12879,uu____12880) ->
                   let head1 =
                     let uu____12884 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12884 FStar_Pervasives.fst in
                   let head2 =
                     let uu____12915 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____12915 FStar_Pervasives.fst in
                   let uu____12943 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____12943
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____12952 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____12952
                      then
                        let guard =
                          let uu____12959 =
                            let uu____12960 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____12960 = FStar_Syntax_Util.Equal in
                          if uu____12959
                          then None
                          else
                            (let uu____12963 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____12963) in
                        let uu____12965 = solve_prob orig guard [] wl in
                        solve env uu____12965
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12968,uu____12969) ->
                   let head1 =
                     let uu____12973 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____12973 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13004 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13004 FStar_Pervasives.fst in
                   let uu____13032 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13032
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13041 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13041
                      then
                        let guard =
                          let uu____13048 =
                            let uu____13049 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13049 = FStar_Syntax_Util.Equal in
                          if uu____13048
                          then None
                          else
                            (let uu____13052 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____13052) in
                        let uu____13054 = solve_prob orig guard [] wl in
                        solve env uu____13054
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____13057,uu____13058) ->
                   let head1 =
                     let uu____13062 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13062 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13093 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13093 FStar_Pervasives.fst in
                   let uu____13121 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13121
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13130 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13130
                      then
                        let guard =
                          let uu____13137 =
                            let uu____13138 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13138 = FStar_Syntax_Util.Equal in
                          if uu____13137
                          then None
                          else
                            (let uu____13141 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____13141) in
                        let uu____13143 = solve_prob orig guard [] wl in
                        solve env uu____13143
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13146,uu____13147) ->
                   let head1 =
                     let uu____13160 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13160 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13191 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13191 FStar_Pervasives.fst in
                   let uu____13219 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13219
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13228 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13228
                      then
                        let guard =
                          let uu____13235 =
                            let uu____13236 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13236 = FStar_Syntax_Util.Equal in
                          if uu____13235
                          then None
                          else
                            (let uu____13239 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____13239) in
                        let uu____13241 = solve_prob orig guard [] wl in
                        solve env uu____13241
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13244,FStar_Syntax_Syntax.Tm_match uu____13245) ->
                   let head1 =
                     let uu____13264 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13264 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13295 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13295 FStar_Pervasives.fst in
                   let uu____13323 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13323
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13332 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13332
                      then
                        let guard =
                          let uu____13339 =
                            let uu____13340 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13340 = FStar_Syntax_Util.Equal in
                          if uu____13339
                          then None
                          else
                            (let uu____13343 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13343) in
                        let uu____13345 = solve_prob orig guard [] wl in
                        solve env uu____13345
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13348,FStar_Syntax_Syntax.Tm_uinst uu____13349) ->
                   let head1 =
                     let uu____13357 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13357 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13388 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13388 FStar_Pervasives.fst in
                   let uu____13416 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13416
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13425 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13425
                      then
                        let guard =
                          let uu____13432 =
                            let uu____13433 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13433 = FStar_Syntax_Util.Equal in
                          if uu____13432
                          then None
                          else
                            (let uu____13436 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_88  -> Some _0_88)
                               uu____13436) in
                        let uu____13438 = solve_prob orig guard [] wl in
                        solve env uu____13438
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13441,FStar_Syntax_Syntax.Tm_name uu____13442) ->
                   let head1 =
                     let uu____13446 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13446 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13477 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13477 FStar_Pervasives.fst in
                   let uu____13505 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13505
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13514 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13514
                      then
                        let guard =
                          let uu____13521 =
                            let uu____13522 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13522 = FStar_Syntax_Util.Equal in
                          if uu____13521
                          then None
                          else
                            (let uu____13525 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_89  -> Some _0_89)
                               uu____13525) in
                        let uu____13527 = solve_prob orig guard [] wl in
                        solve env uu____13527
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13530,FStar_Syntax_Syntax.Tm_constant uu____13531) ->
                   let head1 =
                     let uu____13535 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13535 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13566 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13566 FStar_Pervasives.fst in
                   let uu____13594 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13594
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13603 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13603
                      then
                        let guard =
                          let uu____13610 =
                            let uu____13611 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13611 = FStar_Syntax_Util.Equal in
                          if uu____13610
                          then None
                          else
                            (let uu____13614 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                               uu____13614) in
                        let uu____13616 = solve_prob orig guard [] wl in
                        solve env uu____13616
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13619,FStar_Syntax_Syntax.Tm_fvar uu____13620) ->
                   let head1 =
                     let uu____13624 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13624 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13655 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13655 FStar_Pervasives.fst in
                   let uu____13683 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13683
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13692 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13692
                      then
                        let guard =
                          let uu____13699 =
                            let uu____13700 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13700 = FStar_Syntax_Util.Equal in
                          if uu____13699
                          then None
                          else
                            (let uu____13703 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_91  -> Some _0_91)
                               uu____13703) in
                        let uu____13705 = solve_prob orig guard [] wl in
                        solve env uu____13705
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13708,FStar_Syntax_Syntax.Tm_app uu____13709) ->
                   let head1 =
                     let uu____13722 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____13722 FStar_Pervasives.fst in
                   let head2 =
                     let uu____13753 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____13753 FStar_Pervasives.fst in
                   let uu____13781 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____13781
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____13790 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____13790
                      then
                        let guard =
                          let uu____13797 =
                            let uu____13798 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____13798 = FStar_Syntax_Util.Equal in
                          if uu____13797
                          then None
                          else
                            (let uu____13801 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_92  -> Some _0_92)
                               uu____13801) in
                        let uu____13803 = solve_prob orig guard [] wl in
                        solve env uu____13803
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13807,uu____13808),uu____13809) ->
                   solve_t' env
                     (let uu___175_13838 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13838.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13838.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_13838.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_13838.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13838.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13838.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13838.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13838.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13838.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13841,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13843,uu____13844)) ->
                   solve_t' env
                     (let uu___176_13873 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13873.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_13873.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13873.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___176_13873.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13873.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13873.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13873.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13873.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13873.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13874,uu____13875) ->
                   let uu____13883 =
                     let uu____13884 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13885 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13884
                       uu____13885 in
                   failwith uu____13883
               | (FStar_Syntax_Syntax.Tm_meta uu____13886,uu____13887) ->
                   let uu____13892 =
                     let uu____13893 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13894 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13893
                       uu____13894 in
                   failwith uu____13892
               | (FStar_Syntax_Syntax.Tm_delayed uu____13895,uu____13896) ->
                   let uu____13917 =
                     let uu____13918 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13919 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13918
                       uu____13919 in
                   failwith uu____13917
               | (uu____13920,FStar_Syntax_Syntax.Tm_meta uu____13921) ->
                   let uu____13926 =
                     let uu____13927 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13928 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13927
                       uu____13928 in
                   failwith uu____13926
               | (uu____13929,FStar_Syntax_Syntax.Tm_delayed uu____13930) ->
                   let uu____13951 =
                     let uu____13952 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13953 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13952
                       uu____13953 in
                   failwith uu____13951
               | (uu____13954,FStar_Syntax_Syntax.Tm_let uu____13955) ->
                   let uu____13963 =
                     let uu____13964 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____13965 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13964
                       uu____13965 in
                   failwith uu____13963
               | uu____13966 -> giveup env "head tag mismatch" orig)))
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
          (let uu____13998 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____13998
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____14006  ->
                  fun uu____14007  ->
                    match (uu____14006, uu____14007) with
                    | ((a1,uu____14017),(a2,uu____14019)) ->
                        let uu____14024 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_93  -> FStar_TypeChecker_Common.TProb _0_93)
                          uu____14024)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____14030 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____14030 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____14050 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____14057)::[] -> wp1
              | uu____14070 ->
                  let uu____14076 =
                    let uu____14077 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____14077 in
                  failwith uu____14076 in
            let uu____14080 =
              let uu____14086 =
                let uu____14087 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____14087 in
              [uu____14086] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____14080;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____14088 = lift_c1 () in solve_eq uu____14088 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___133_14092  ->
                       match uu___133_14092 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____14093 -> false)) in
             let uu____14094 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____14118)::uu____14119,(wp2,uu____14121)::uu____14122)
                   -> (wp1, wp2)
               | uu____14163 ->
                   let uu____14176 =
                     let uu____14177 =
                       let uu____14180 =
                         let uu____14181 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____14182 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14181 uu____14182 in
                       (uu____14180, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____14177 in
                   raise uu____14176 in
             match uu____14094 with
             | (wpc1,wpc2) ->
                 let uu____14199 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____14199
                 then
                   let uu____14202 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____14202 wl
                 else
                   (let uu____14206 =
                      let uu____14210 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____14210 in
                    match uu____14206 with
                    | (c2_decl,qualifiers) ->
                        let uu____14222 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____14222
                        then
                          let c1_repr =
                            let uu____14225 =
                              let uu____14226 =
                                let uu____14227 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____14227 in
                              let uu____14228 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14226 uu____14228 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14225 in
                          let c2_repr =
                            let uu____14230 =
                              let uu____14231 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____14232 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14231 uu____14232 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14230 in
                          let prob =
                            let uu____14234 =
                              let uu____14237 =
                                let uu____14238 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____14239 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14238
                                  uu____14239 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14237 in
                            FStar_TypeChecker_Common.TProb uu____14234 in
                          let wl1 =
                            let uu____14241 =
                              let uu____14243 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____14243 in
                            solve_prob orig uu____14241 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14250 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____14250
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14252 =
                                     let uu____14255 =
                                       let uu____14256 =
                                         let uu____14266 =
                                           let uu____14267 =
                                             let uu____14268 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____14268] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14267 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____14269 =
                                           let uu____14271 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____14272 =
                                             let uu____14274 =
                                               let uu____14275 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14275 in
                                             [uu____14274] in
                                           uu____14271 :: uu____14272 in
                                         (uu____14266, uu____14269) in
                                       FStar_Syntax_Syntax.Tm_app uu____14256 in
                                     FStar_Syntax_Syntax.mk uu____14255 in
                                   uu____14252
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14286 =
                                    let uu____14289 =
                                      let uu____14290 =
                                        let uu____14300 =
                                          let uu____14301 =
                                            let uu____14302 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____14302] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14301 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____14303 =
                                          let uu____14305 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____14306 =
                                            let uu____14308 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____14309 =
                                              let uu____14311 =
                                                let uu____14312 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14312 in
                                              [uu____14311] in
                                            uu____14308 :: uu____14309 in
                                          uu____14305 :: uu____14306 in
                                        (uu____14300, uu____14303) in
                                      FStar_Syntax_Syntax.Tm_app uu____14290 in
                                    FStar_Syntax_Syntax.mk uu____14289 in
                                  uu____14286
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____14323 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_94  ->
                                  FStar_TypeChecker_Common.TProb _0_94)
                               uu____14323 in
                           let wl1 =
                             let uu____14329 =
                               let uu____14331 =
                                 let uu____14334 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____14334 g in
                               FStar_All.pipe_left (fun _0_95  -> Some _0_95)
                                 uu____14331 in
                             solve_prob orig uu____14329 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____14344 = FStar_Util.physical_equality c1 c2 in
        if uu____14344
        then
          let uu____14345 = solve_prob orig None [] wl in
          solve env uu____14345
        else
          ((let uu____14348 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____14348
            then
              let uu____14349 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____14350 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14349
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14350
            else ());
           (let uu____14352 =
              let uu____14355 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____14356 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____14355, uu____14356) in
            match uu____14352 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14360),FStar_Syntax_Syntax.Total
                    (t2,uu____14362)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14375 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14375 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14378,FStar_Syntax_Syntax.Total uu____14379) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14391),FStar_Syntax_Syntax.Total
                    (t2,uu____14393)) ->
                     let uu____14406 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14406 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14410),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14412)) ->
                     let uu____14425 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14425 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14429),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14431)) ->
                     let uu____14444 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____14444 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14447,FStar_Syntax_Syntax.Comp uu____14448) ->
                     let uu____14454 =
                       let uu___177_14457 = problem in
                       let uu____14460 =
                         let uu____14461 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14461 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14457.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14460;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14457.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14457.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14457.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14457.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14457.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14457.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14457.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14457.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14454 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14462,FStar_Syntax_Syntax.Comp uu____14463) ->
                     let uu____14469 =
                       let uu___177_14472 = problem in
                       let uu____14475 =
                         let uu____14476 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14476 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14472.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14475;
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14472.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___177_14472.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___177_14472.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14472.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14472.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14472.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14472.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14472.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14469 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14477,FStar_Syntax_Syntax.GTotal uu____14478) ->
                     let uu____14484 =
                       let uu___178_14487 = problem in
                       let uu____14490 =
                         let uu____14491 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14491 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14487.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14487.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14487.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14490;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14487.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14487.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14487.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14487.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14487.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14487.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14484 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14492,FStar_Syntax_Syntax.Total uu____14493) ->
                     let uu____14499 =
                       let uu___178_14502 = problem in
                       let uu____14505 =
                         let uu____14506 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14506 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14502.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___178_14502.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14502.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14505;
                         FStar_TypeChecker_Common.element =
                           (uu___178_14502.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14502.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14502.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14502.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14502.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14502.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____14499 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14507,FStar_Syntax_Syntax.Comp uu____14508) ->
                     let uu____14509 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____14509
                     then
                       let uu____14510 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____14510 wl
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
                           (let uu____14520 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____14520
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14522 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____14522 with
                            | None  ->
                                let uu____14524 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14525 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____14525) in
                                if uu____14524
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
                                  (let uu____14528 =
                                     let uu____14529 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____14530 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14529 uu____14530 in
                                   giveup env uu____14528 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14536 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14552  ->
              match uu____14552 with
              | (uu____14559,uu____14560,u,uu____14562,uu____14563,uu____14564)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____14536 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14583 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____14583 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____14593 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14605  ->
                match uu____14605 with
                | (u1,u2) ->
                    let uu____14610 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____14611 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____14610 uu____14611)) in
      FStar_All.pipe_right uu____14593 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14625,[])) -> "{}"
      | uu____14638 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14648 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____14648
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____14651 =
              FStar_List.map
                (fun uu____14655  ->
                   match uu____14655 with
                   | (uu____14658,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____14651 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____14662 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14662 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14707 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____14707
    then
      let uu____14708 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____14709 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14708
        (rel_to_string rel) uu____14709
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
            let uu____14733 =
              let uu____14735 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_96  -> Some _0_96) uu____14735 in
            FStar_Syntax_Syntax.new_bv uu____14733 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____14741 =
              let uu____14743 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_97  -> Some _0_97) uu____14743 in
            let uu____14745 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____14741 uu____14745 in
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
          let uu____14771 = FStar_Options.eager_inference () in
          if uu____14771
          then
            let uu___179_14772 = probs in
            {
              attempting = (uu___179_14772.attempting);
              wl_deferred = (uu___179_14772.wl_deferred);
              ctr = (uu___179_14772.ctr);
              defer_ok = false;
              smt_ok = (uu___179_14772.smt_ok);
              tcenv = (uu___179_14772.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14783 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____14783
              then
                let uu____14784 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____14784
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
          ((let uu____14796 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____14796
            then
              let uu____14797 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14797
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____14801 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____14801
             then
               let uu____14802 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14802
             else ());
            (let f2 =
               let uu____14805 =
                 let uu____14806 = FStar_Syntax_Util.unmeta f1 in
                 uu____14806.FStar_Syntax_Syntax.n in
               match uu____14805 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14810 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___180_14811 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___180_14811.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___180_14811.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___180_14811.FStar_TypeChecker_Env.implicits)
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
            let uu____14829 =
              let uu____14830 =
                let uu____14831 =
                  let uu____14832 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____14832
                    (fun _0_98  -> FStar_TypeChecker_Common.NonTrivial _0_98) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14831;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____14830 in
            FStar_All.pipe_left (fun _0_99  -> Some _0_99) uu____14829
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14869 =
        let uu____14870 =
          let uu____14871 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____14871
            (fun _0_100  -> FStar_TypeChecker_Common.NonTrivial _0_100) in
        {
          FStar_TypeChecker_Env.guard_f = uu____14870;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____14869
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
          (let uu____14901 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14901
           then
             let uu____14902 = FStar_Syntax_Print.term_to_string t1 in
             let uu____14903 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14902
               uu____14903
           else ());
          (let prob =
             let uu____14906 =
               let uu____14909 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14909 in
             FStar_All.pipe_left
               (fun _0_101  -> FStar_TypeChecker_Common.TProb _0_101)
               uu____14906 in
           let g =
             let uu____14914 =
               let uu____14916 = singleton' env prob smt_ok in
               solve_and_commit env uu____14916 (fun uu____14917  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____14914 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14934 = try_teq true env t1 t2 in
        match uu____14934 with
        | None  ->
            let uu____14936 =
              let uu____14937 =
                let uu____14940 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____14941 = FStar_TypeChecker_Env.get_range env in
                (uu____14940, uu____14941) in
              FStar_Errors.Error uu____14937 in
            raise uu____14936
        | Some g ->
            ((let uu____14944 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____14944
              then
                let uu____14945 = FStar_Syntax_Print.term_to_string t1 in
                let uu____14946 = FStar_Syntax_Print.term_to_string t2 in
                let uu____14947 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14945
                  uu____14946 uu____14947
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
          (let uu____14967 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____14967
           then
             let uu____14968 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____14969 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14968
               uu____14969
           else ());
          (let uu____14971 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____14971 with
           | (prob,x) ->
               let g =
                 let uu____14979 =
                   let uu____14981 = singleton' env prob smt_ok in
                   solve_and_commit env uu____14981
                     (fun uu____14982  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____14979 in
               ((let uu____14988 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____14988
                 then
                   let uu____14989 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____14990 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____14991 =
                     let uu____14992 = FStar_Util.must g in
                     guard_to_string env uu____14992 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14989 uu____14990 uu____14991
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
          let uu____15023 = FStar_TypeChecker_Env.get_range env in
          let uu____15024 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____15023 uu____15024
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____15039 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____15039
         then
           let uu____15040 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____15041 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____15040
             uu____15041
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____15046 =
             let uu____15049 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____15049 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_102  -> FStar_TypeChecker_Common.CProb _0_102)
             uu____15046 in
         let uu____15052 =
           let uu____15054 = singleton env prob in
           solve_and_commit env uu____15054 (fun uu____15055  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____15052)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____15077  ->
        match uu____15077 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____15102 =
                 let uu____15103 =
                   let uu____15106 =
                     let uu____15107 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____15108 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____15107 uu____15108 in
                   let uu____15109 = FStar_TypeChecker_Env.get_range env in
                   (uu____15106, uu____15109) in
                 FStar_Errors.Error uu____15103 in
               raise uu____15102) in
            let equiv1 v1 v' =
              let uu____15117 =
                let uu____15120 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____15121 = FStar_Syntax_Subst.compress_univ v' in
                (uu____15120, uu____15121) in
              match uu____15117 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____15128 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____15142 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____15142 with
                      | FStar_Syntax_Syntax.U_unif uu____15146 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____15157  ->
                                    match uu____15157 with
                                    | (u,v') ->
                                        let uu____15163 = equiv1 v1 v' in
                                        if uu____15163
                                        then
                                          let uu____15165 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____15165 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____15175 -> [])) in
            let uu____15178 =
              let wl =
                let uu___181_15181 = empty_worklist env in
                {
                  attempting = (uu___181_15181.attempting);
                  wl_deferred = (uu___181_15181.wl_deferred);
                  ctr = (uu___181_15181.ctr);
                  defer_ok = false;
                  smt_ok = (uu___181_15181.smt_ok);
                  tcenv = (uu___181_15181.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15188  ->
                      match uu____15188 with
                      | (lb,v1) ->
                          let uu____15193 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____15193 with
                           | USolved wl1 -> ()
                           | uu____15195 -> fail lb v1))) in
            let rec check_ineq uu____15201 =
              match uu____15201 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15208) -> true
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
                      uu____15219,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15221,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15226) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15230,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15235 -> false) in
            let uu____15238 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15244  ->
                      match uu____15244 with
                      | (u,v1) ->
                          let uu____15249 = check_ineq (u, v1) in
                          if uu____15249
                          then true
                          else
                            ((let uu____15252 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____15252
                              then
                                let uu____15253 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____15254 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____15253
                                  uu____15254
                              else ());
                             false))) in
            if uu____15238
            then ()
            else
              ((let uu____15258 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____15258
                then
                  ((let uu____15260 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15260);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____15266 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15266))
                else ());
               (let uu____15272 =
                  let uu____15273 =
                    let uu____15276 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15276) in
                  FStar_Errors.Error uu____15273 in
                raise uu____15272))
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
      let fail uu____15313 =
        match uu____15313 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____15323 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15323
       then
         let uu____15324 = wl_to_string wl in
         let uu____15325 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15324 uu____15325
       else ());
      (let g1 =
         let uu____15340 = solve_and_commit env wl fail in
         match uu____15340 with
         | Some [] ->
             let uu___182_15347 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___182_15347.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___182_15347.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___182_15347.FStar_TypeChecker_Env.implicits)
             }
         | uu____15350 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___183_15353 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___183_15353.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___183_15353.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___183_15353.FStar_TypeChecker_Env.implicits)
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
            let uu___184_15383 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___184_15383.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___184_15383.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___184_15383.FStar_TypeChecker_Env.implicits)
            } in
          let uu____15384 =
            let uu____15385 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____15385 in
          if uu____15384
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15391 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____15391
                   then
                     let uu____15392 = FStar_TypeChecker_Env.get_range env in
                     let uu____15393 =
                       let uu____15394 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15394 in
                     FStar_Errors.diag uu____15392 uu____15393
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding] env vc in
                   let uu____15397 = check_trivial vc1 in
                   match uu____15397 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____15404 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____15404
                           then
                             let uu____15405 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____15406 =
                               let uu____15407 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15407 in
                             FStar_Errors.diag uu____15405 uu____15406
                           else ());
                          (let vcs =
                             let uu____15413 = FStar_Options.use_tactics () in
                             if uu____15413
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15427  ->
                                   match uu____15427 with
                                   | (env1,goal) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify]
                                           env1 goal in
                                       let uu____15433 = check_trivial goal1 in
                                       (match uu____15433 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15435 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____15435
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15440 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____15440
                                              then
                                                let uu____15441 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____15442 =
                                                  let uu____15443 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____15444 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15443 uu____15444 in
                                                FStar_Errors.diag uu____15441
                                                  uu____15442
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
      let uu____15454 = discharge_guard' None env g false in
      match uu____15454 with
      | Some g1 -> g1
      | None  ->
          let uu____15459 =
            let uu____15460 =
              let uu____15463 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____15463) in
            FStar_Errors.Error uu____15460 in
          raise uu____15459
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15472 = discharge_guard' None env g true in
      match uu____15472 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15485 = FStar_Syntax_Unionfind.find u in
      match uu____15485 with | None  -> true | uu____15487 -> false in
    let rec until_fixpoint acc implicits =
      let uu____15500 = acc in
      match uu____15500 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15546 = hd1 in
               (match uu____15546 with
                | (uu____15553,env,u,tm,k,r) ->
                    let uu____15559 = unresolved u in
                    if uu____15559
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____15577 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____15577
                        then
                          let uu____15578 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____15579 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____15580 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15578 uu____15579 uu____15580
                        else ());
                       (let uu____15582 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___185_15586 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___185_15586.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___185_15586.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___185_15586.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___185_15586.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___185_15586.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___185_15586.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___185_15586.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___185_15586.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___185_15586.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___185_15586.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___185_15586.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___185_15586.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___185_15586.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___185_15586.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___185_15586.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___185_15586.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___185_15586.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___185_15586.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___185_15586.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___185_15586.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___185_15586.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___185_15586.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___185_15586.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___185_15586.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___185_15586.FStar_TypeChecker_Env.synth)
                             }) tm1 in
                        match uu____15582 with
                        | (uu____15587,uu____15588,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___186_15591 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___186_15591.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___186_15591.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___186_15591.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____15594 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15598  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____15594 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___187_15613 = g in
    let uu____15614 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___187_15613.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___187_15613.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___187_15613.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15614
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15644 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____15644 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15651 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15651
      | (reason,uu____15653,uu____15654,e,t,r)::uu____15658 ->
          let uu____15672 =
            let uu____15673 = FStar_Syntax_Print.term_to_string t in
            let uu____15674 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15673 uu____15674 in
          FStar_Errors.err r uu____15672
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___188_15683 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___188_15683.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___188_15683.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___188_15683.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15704 = try_teq false env t1 t2 in
        match uu____15704 with
        | None  -> false
        | Some g ->
            let uu____15707 = discharge_guard' None env g false in
            (match uu____15707 with
             | Some uu____15711 -> true
             | None  -> false)