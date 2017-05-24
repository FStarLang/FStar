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
            let uu___133_64 = g1 in
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
                (uu___133_64.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_64.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_64.FStar_TypeChecker_Env.implicits)
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
          let uu___134_104 = g in
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
              (uu___134_104.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___134_104.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___134_104.FStar_TypeChecker_Env.implicits)
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
          let uu___135_145 = g in
          let uu____146 =
            let uu____147 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____147 in
          {
            FStar_TypeChecker_Env.guard_f = uu____146;
            FStar_TypeChecker_Env.deferred =
              (uu___135_145.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_145.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_145.FStar_TypeChecker_Env.implicits)
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
                       let uu____248 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____248
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f in
            let uu___136_250 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___136_250.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_250.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_250.FStar_TypeChecker_Env.implicits)
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
            let uu___137_277 = g in
            let uu____278 =
              let uu____279 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____279 in
            {
              FStar_TypeChecker_Env.guard_f = uu____278;
              FStar_TypeChecker_Env.deferred =
                (uu___137_277.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_277.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_277.FStar_TypeChecker_Env.implicits)
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
        | uu____320 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____335 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____335 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r in
            let uu____351 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____351, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____380 = FStar_Syntax_Util.type_u () in
        match uu____380 with
        | (t_type,u) ->
            let uu____385 =
              let uu____388 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____388 t_type in
            (match uu____385 with
             | (tt,uu____390) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____411 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____437 -> false
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
    match projectee with | Success _0 -> true | uu____517 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____531 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____548 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____552 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____556 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_573  ->
    match uu___105_573 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____586 =
    let uu____587 = FStar_Syntax_Subst.compress t in
    uu____587.FStar_Syntax_Syntax.n in
  match uu____586 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____604 = FStar_Syntax_Print.uvar_to_string u in
      let uu____608 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____604 uu____608
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____611;
         FStar_Syntax_Syntax.pos = uu____612;
         FStar_Syntax_Syntax.vars = uu____613;_},args)
      ->
      let uu____641 = FStar_Syntax_Print.uvar_to_string u in
      let uu____645 = FStar_Syntax_Print.term_to_string ty in
      let uu____646 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____641 uu____645 uu____646
  | uu____647 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_653  ->
      match uu___106_653 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____657 =
            let uu____659 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____660 =
              let uu____662 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____663 =
                let uu____665 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____666 =
                  let uu____668 =
                    let uu____670 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____671 =
                      let uu____673 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____674 =
                        let uu____676 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____677 =
                          let uu____679 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____679] in
                        uu____676 :: uu____677 in
                      uu____673 :: uu____674 in
                    uu____670 :: uu____671 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____668 in
                uu____665 :: uu____666 in
              uu____662 :: uu____663 in
            uu____659 :: uu____660 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____657
      | FStar_TypeChecker_Common.CProb p ->
          let uu____684 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____685 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____684
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____685
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_691  ->
      match uu___107_691 with
      | UNIV (u,t) ->
          let x =
            let uu____695 = FStar_Options.hide_uvar_nums () in
            if uu____695
            then "?"
            else
              (let uu____697 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____697 FStar_Util.string_of_int) in
          let uu____699 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____699
      | TERM ((u,uu____701),t) ->
          let x =
            let uu____706 = FStar_Options.hide_uvar_nums () in
            if uu____706
            then "?"
            else
              (let uu____708 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____708 FStar_Util.string_of_int) in
          let uu____712 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____712
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____721 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____721 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____729 =
      let uu____731 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____731
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____729 (FStar_String.concat ", ")
let args_to_string args =
  let uu____749 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____757  ->
            match uu____757 with
            | (x,uu____761) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____749 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____766 =
      let uu____767 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____767 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____766;
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
        let uu___138_780 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___138_780.wl_deferred);
          ctr = (uu___138_780.ctr);
          defer_ok = (uu___138_780.defer_ok);
          smt_ok;
          tcenv = (uu___138_780.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___139_805 = empty_worklist env in
  let uu____806 = FStar_List.map FStar_Pervasives.snd g in
  {
    attempting = uu____806;
    wl_deferred = (uu___139_805.wl_deferred);
    ctr = (uu___139_805.ctr);
    defer_ok = false;
    smt_ok = (uu___139_805.smt_ok);
    tcenv = (uu___139_805.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_818 = wl in
        {
          attempting = (uu___140_818.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_818.ctr);
          defer_ok = (uu___140_818.defer_ok);
          smt_ok = (uu___140_818.smt_ok);
          tcenv = (uu___140_818.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___141_830 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_830.wl_deferred);
        ctr = (uu___141_830.ctr);
        defer_ok = (uu___141_830.defer_ok);
        smt_ok = (uu___141_830.smt_ok);
        tcenv = (uu___141_830.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____841 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____841
         then
           let uu____842 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____842
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_846  ->
    match uu___108_846 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___142_862 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_862.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_862.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_862.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_862.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_862.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_862.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_862.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_883  ->
    match uu___109_883 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_899  ->
      match uu___110_899 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_902  ->
    match uu___111_902 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_911  ->
    match uu___112_911 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_921  ->
    match uu___113_921 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_931  ->
    match uu___114_931 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___115_942  ->
    match uu___115_942 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_953  ->
    match uu___116_953 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_962  ->
    match uu___117_962 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____976 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____976 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____987  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1037 = next_pid () in
  let uu____1038 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1037;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1038;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1085 = next_pid () in
  let uu____1086 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1085;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1086;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1127 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1127;
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
        let uu____1179 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1179
        then
          let uu____1180 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1181 = prob_to_string env d in
          let uu____1182 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1180 uu____1181 uu____1182 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1187 -> failwith "impossible" in
           let uu____1188 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1196 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1197 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1196, uu____1197)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1201 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1202 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1201, uu____1202) in
           match uu____1188 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1211  ->
            match uu___118_1211 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1218 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1221),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar -> uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1244  ->
           match uu___119_1244 with
           | UNIV uu____1246 -> None
           | TERM ((u,uu____1250),t) ->
               let uu____1254 = FStar_Unionfind.equivalent uv u in
               if uu____1254 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1273  ->
           match uu___120_1273 with
           | UNIV (u',t) ->
               let uu____1277 = FStar_Unionfind.equivalent u u' in
               if uu____1277 then Some t else None
           | uu____1281 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1288 =
        let uu____1289 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1289 in
      FStar_Syntax_Subst.compress uu____1288
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1296 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1296
let norm_arg env t = let uu____1315 = sn env (fst t) in (uu____1315, (snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1332  ->
              match uu____1332 with
              | (x,imp) ->
                  let uu____1339 =
                    let uu___143_1340 = x in
                    let uu____1341 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1340.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1340.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1341
                    } in
                  (uu____1339, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1356 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1356
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1359 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1359
        | uu____1361 -> u2 in
      let uu____1362 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1362
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1469 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1469 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1481;
               FStar_Syntax_Syntax.pos = uu____1482;
               FStar_Syntax_Syntax.vars = uu____1483;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1504 =
                 let uu____1505 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1506 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1505
                   uu____1506 in
               failwith uu____1504)
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1541 =
             let uu____1542 = FStar_Syntax_Subst.compress t1' in
             uu____1542.FStar_Syntax_Syntax.n in
           match uu____1541 with
           | FStar_Syntax_Syntax.Tm_refine uu____1554 -> aux true t1'
           | uu____1559 -> (t11, None))
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
        let uu____1594 =
          let uu____1595 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1596 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1595
            uu____1596 in
        failwith uu____1594 in
  let uu____1606 = whnf env t1 in aux false uu____1606
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1615 =
        let uu____1625 = empty_worklist env in
        base_and_refinement env uu____1625 t in
      FStar_All.pipe_right uu____1615 FStar_Pervasives.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1649 = FStar_Syntax_Syntax.null_bv t in
    (uu____1649, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1669 = base_and_refinement env wl t in
  match uu____1669 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____1728 =
  match uu____1728 with
  | (t_base,refopt) ->
      let uu____1742 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____1742 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_1766  ->
      match uu___121_1766 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1770 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1771 =
            let uu____1772 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____1772 in
          let uu____1773 =
            let uu____1774 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____1774 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1770 uu____1771
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1773
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1778 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1779 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____1780 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1778 uu____1779
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1780
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____1784 =
      let uu____1786 =
        let uu____1788 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1798  ->
                  match uu____1798 with | (uu____1802,uu____1803,x) -> x)) in
        FStar_List.append wl.attempting uu____1788 in
      FStar_List.map (wl_prob_to_string wl) uu____1786 in
    FStar_All.pipe_right uu____1784 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1821 =
          let uu____1831 =
            let uu____1832 = FStar_Syntax_Subst.compress k in
            uu____1832.FStar_Syntax_Syntax.n in
          match uu____1831 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____1873 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____1873)
              else
                (let uu____1887 = FStar_Syntax_Util.abs_formals t in
                 match uu____1887 with
                 | (ys',t1,uu____1908) ->
                     let uu____1921 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____1921))
          | uu____1942 ->
              let uu____1943 =
                let uu____1949 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____1949) in
              ((ys, t), uu____1943) in
        match uu____1821 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2004 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2004 c in
               let uu____2006 =
                 let uu____2013 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____2013 (fun _0_37  -> Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____2006)
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
            let uu____2064 = p_guard prob in
            match uu____2064 with
            | (uu____2067,uv) ->
                ((let uu____2070 =
                    let uu____2071 = FStar_Syntax_Subst.compress uv in
                    uu____2071.FStar_Syntax_Syntax.n in
                  match uu____2070 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2091 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2091
                        then
                          let uu____2092 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2093 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2094 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2092
                            uu____2093 uu____2094
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2098 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2101 = wl in
                  {
                    attempting = (uu___144_2101.attempting);
                    wl_deferred = (uu___144_2101.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2101.defer_ok);
                    smt_ok = (uu___144_2101.smt_ok);
                    tcenv = (uu___144_2101.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2114 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2114
         then
           let uu____2115 = FStar_Util.string_of_int pid in
           let uu____2116 =
             let uu____2117 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2117 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2115 uu____2116
         else ());
        commit sol;
        (let uu___145_2122 = wl in
         {
           attempting = (uu___145_2122.attempting);
           wl_deferred = (uu___145_2122.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2122.defer_ok);
           smt_ok = (uu___145_2122.smt_ok);
           tcenv = (uu___145_2122.tcenv)
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
            | (uu____2151,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2159 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2159 in
          (let uu____2165 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2165
           then
             let uu____2166 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2167 =
               let uu____2168 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2168 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2166 uu____2167
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2193 =
    let uu____2197 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2197 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2193
    (FStar_Util.for_some
       (fun uu____2218  ->
          match uu____2218 with
          | (uv,uu____2226) -> FStar_Unionfind.equivalent uv (fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2270 = occurs wl uk t in Prims.op_Negation uu____2270 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2275 =
         let uu____2276 = FStar_Syntax_Print.uvar_to_string (fst uk) in
         let uu____2280 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2276 uu____2280 in
       Some uu____2275) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2328 = occurs_check env wl uk t in
  match uu____2328 with
  | (occurs_ok,msg) ->
      let uu____2345 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2345, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____2409 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2433  ->
            fun uu____2434  ->
              match (uu____2433, uu____2434) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2477 =
                    let uu____2478 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2478 in
                  if uu____2477
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2492 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2492
                     then
                       let uu____2499 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2499)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2409 with | (isect,uu____2521) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2570  ->
          fun uu____2571  ->
            match (uu____2570, uu____2571) with
            | ((a,uu____2581),(b,uu____2583)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2627 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2633  ->
                match uu____2633 with
                | (b,uu____2637) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2627 then None else Some (a, (snd hd1))
  | uu____2646 -> None
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
            let uu____2689 = pat_var_opt env seen hd1 in
            (match uu____2689 with
             | None  ->
                 ((let uu____2697 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2697
                   then
                     let uu____2698 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2698
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2710 =
      let uu____2711 = FStar_Syntax_Subst.compress t in
      uu____2711.FStar_Syntax_Syntax.n in
    match uu____2710 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2727 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2789;
         FStar_Syntax_Syntax.pos = uu____2790;
         FStar_Syntax_Syntax.vars = uu____2791;_},args)
      -> (t, uv, k, args)
  | uu____2832 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____2886 = destruct_flex_t t in
  match uu____2886 with
  | (t1,uv,k,args) ->
      let uu____2954 = pat_vars env [] args in
      (match uu____2954 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3010 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option*
  FStar_Syntax_Syntax.delta_depth option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3058 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option* FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3081 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3085 -> false
let head_match: match_result -> match_result =
  fun uu___122_3088  ->
    match uu___122_3088 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3097 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3110 ->
          let uu____3111 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3111 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3121 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
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
          let uu____3189 = fv_delta_depth env fv in Some uu____3189
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
            let uu____3208 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3208
            then FullMatch
            else
              (let uu____3210 =
                 let uu____3215 =
                   let uu____3217 = fv_delta_depth env f in Some uu____3217 in
                 let uu____3218 =
                   let uu____3220 = fv_delta_depth env g in Some uu____3220 in
                 (uu____3215, uu____3218) in
               MisMatch uu____3210)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3224),FStar_Syntax_Syntax.Tm_uinst (g,uu____3226)) ->
            let uu____3235 = head_matches env f g in
            FStar_All.pipe_right uu____3235 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3242),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3244)) ->
            let uu____3269 = FStar_Unionfind.equivalent uv uv' in
            if uu____3269 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3277),FStar_Syntax_Syntax.Tm_refine (y,uu____3279)) ->
            let uu____3288 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3288 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3290),uu____3291) ->
            let uu____3296 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3296 head_match
        | (uu____3297,FStar_Syntax_Syntax.Tm_refine (x,uu____3299)) ->
            let uu____3304 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3304 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3310),FStar_Syntax_Syntax.Tm_app (head',uu____3312))
            ->
            let uu____3341 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3341 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3343),uu____3344) ->
            let uu____3359 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3359 head_match
        | (uu____3360,FStar_Syntax_Syntax.Tm_app (head1,uu____3362)) ->
            let uu____3377 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3377 head_match
        | uu____3378 ->
            let uu____3381 =
              let uu____3386 = delta_depth_of_term env t11 in
              let uu____3388 = delta_depth_of_term env t21 in
              (uu____3386, uu____3388) in
            MisMatch uu____3381
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3424 = FStar_Syntax_Util.head_and_args t in
    match uu____3424 with
    | (head1,uu____3436) ->
        let uu____3451 =
          let uu____3452 = FStar_Syntax_Util.un_uinst head1 in
          uu____3452.FStar_Syntax_Syntax.n in
        (match uu____3451 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3457 =
               let uu____3458 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3458 FStar_Option.isSome in
             if uu____3457
             then
               let uu____3472 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3472 (fun _0_38  -> Some _0_38)
             else None
         | uu____3475 -> None) in
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
          (let uu____3555 =
             let uu____3560 = maybe_inline t11 in
             let uu____3562 = maybe_inline t21 in (uu____3560, uu____3562) in
           match uu____3555 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3587 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____3587 with
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
        let uu____3602 =
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
             let uu____3610 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____3610)) in
        (match uu____3602 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3618 -> fail r
    | uu____3623 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3648 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3678 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3693 = FStar_Syntax_Util.type_u () in
      match uu____3693 with
      | (t,uu____3697) ->
          let uu____3698 = new_uvar r binders t in fst uu____3698
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3707 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____3707 FStar_Pervasives.fst
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
        let uu____3749 = head_matches env t1 t' in
        match uu____3749 with
        | MisMatch uu____3750 -> false
        | uu____3755 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3815,imp),T (t2,uu____3818)) -> (t2, imp)
                     | uu____3835 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3875  ->
                    match uu____3875 with
                    | (t2,uu____3883) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3916 = failwith "Bad reconstruction" in
          let uu____3917 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3917 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3970))::tcs2) ->
                       aux
                         (((let uu___146_3992 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_3992.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_3992.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4002 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_4033 =
                 match uu___123_4033 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4096 = decompose1 [] bs1 in
               (rebuild, matches, uu____4096))
      | uu____4124 ->
          let rebuild uu___124_4129 =
            match uu___124_4129 with
            | [] -> t1
            | uu____4131 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4150  ->
    match uu___125_4150 with
    | T (t,uu____4152) -> t
    | uu____4161 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4164  ->
    match uu___126_4164 with
    | T (t,uu____4166) -> FStar_Syntax_Syntax.as_arg t
    | uu____4175 -> failwith "Impossible"
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
              | (uu____4244,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4263 = new_uvar r scope1 k in
                  (match uu____4263 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4275 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
                       let uu____4290 =
                         let uu____4291 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4291 in
                       ((T (gi_xs, mk_kind)), uu____4290))
              | (uu____4300,uu____4301,C uu____4302) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4389 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4400;
                         FStar_Syntax_Syntax.pos = uu____4401;
                         FStar_Syntax_Syntax.vars = uu____4402;_})
                        ->
                        let uu____4417 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4417 with
                         | (T (gi_xs,uu____4433),prob) ->
                             let uu____4443 =
                               let uu____4444 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4444 in
                             (uu____4443, [prob])
                         | uu____4446 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4456;
                         FStar_Syntax_Syntax.pos = uu____4457;
                         FStar_Syntax_Syntax.vars = uu____4458;_})
                        ->
                        let uu____4473 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4473 with
                         | (T (gi_xs,uu____4489),prob) ->
                             let uu____4499 =
                               let uu____4500 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____4500 in
                             (uu____4499, [prob])
                         | uu____4502 -> failwith "impossible")
                    | (uu____4508,uu____4509,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4511;
                         FStar_Syntax_Syntax.pos = uu____4512;
                         FStar_Syntax_Syntax.vars = uu____4513;_})
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
                        let uu____4587 =
                          let uu____4592 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____4592 FStar_List.unzip in
                        (match uu____4587 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____4621 =
                                 let uu____4622 =
                                   let uu____4625 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____4625 un_T in
                                 let uu____4626 =
                                   let uu____4632 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____4632
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____4622;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____4626;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____4621 in
                             ((C gi_xs), sub_probs))
                    | uu____4637 ->
                        let uu____4644 = sub_prob scope1 args q in
                        (match uu____4644 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4389 with
                   | (tc,probs) ->
                       let uu____4662 =
                         match q with
                         | (Some b,uu____4688,uu____4689) ->
                             let uu____4697 =
                               let uu____4701 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____4701 :: args in
                             ((Some b), (b :: scope1), uu____4697)
                         | uu____4719 -> (None, scope1, args) in
                       (match uu____4662 with
                        | (bopt,scope2,args1) ->
                            let uu____4762 = aux scope2 args1 qs2 in
                            (match uu____4762 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____4783 =
                                         let uu____4785 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         f :: uu____4785 in
                                       FStar_Syntax_Util.mk_conj_l uu____4783
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort in
                                       let uu____4798 =
                                         let uu____4800 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f in
                                         let uu____4801 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst)) in
                                         uu____4800 :: uu____4801 in
                                       FStar_Syntax_Util.mk_conj_l uu____4798 in
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
  let uu___147_4854 = p in
  let uu____4857 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____4858 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_4854.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4857;
    FStar_TypeChecker_Common.relation =
      (uu___147_4854.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4858;
    FStar_TypeChecker_Common.element =
      (uu___147_4854.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_4854.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_4854.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_4854.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_4854.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_4854.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____4868 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____4868
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____4873 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____4887 = compress_prob wl pr in
        FStar_All.pipe_right uu____4887 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4893 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____4893 with
           | (lh,uu____4906) ->
               let uu____4921 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____4921 with
                | (rh,uu____4934) ->
                    let uu____4949 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4958,FStar_Syntax_Syntax.Tm_uvar uu____4959)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____4984,uu____4985)
                          ->
                          let uu____4994 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____4994 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5034 ->
                                    let rank =
                                      let uu____5041 = is_top_level_prob prob in
                                      if uu____5041
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5043 =
                                      let uu___148_5046 = tp in
                                      let uu____5049 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5046.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5046.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5046.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5049;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5046.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5046.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5046.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5046.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5046.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5046.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5043)))
                      | (uu____5059,FStar_Syntax_Syntax.Tm_uvar uu____5060)
                          ->
                          let uu____5069 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5069 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5109 ->
                                    let uu____5115 =
                                      let uu___149_5120 = tp in
                                      let uu____5123 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5120.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5123;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5120.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5120.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5120.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5120.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5120.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5120.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5120.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5120.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5115)))
                      | (uu____5139,uu____5140) -> (rigid_rigid, tp) in
                    (match uu____4949 with
                     | (rank,tp1) ->
                         let uu____5151 =
                           FStar_All.pipe_right
                             (let uu___150_5154 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5154.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5154.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5154.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5154.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5154.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5154.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5154.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5154.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5154.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____5151))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5160 =
            FStar_All.pipe_right
              (let uu___151_5163 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5163.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5163.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5163.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5163.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5163.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5163.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5163.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5163.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5163.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____5160)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob option* FStar_TypeChecker_Common.prob
      Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5195 probs =
      match uu____5195 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5225 = rank wl hd1 in
               (match uu____5225 with
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
    match projectee with | UDeferred _0 -> true | uu____5290 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5302 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5314 -> false
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
                        let uu____5351 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5351 with
                        | (k,uu____5355) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5360 -> false)))
            | uu____5361 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5404 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5404 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5407 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5413 =
                     let uu____5414 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5415 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5414
                       uu____5415 in
                   UFailed uu____5413)
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5432 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5432 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5435 ->
                let uu____5438 =
                  let uu____5439 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5440 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5439
                    uu____5440 msg in
                UFailed uu____5438 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5447 =
                let uu____5448 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5449 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5448 uu____5449 in
              failwith uu____5447
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5461 = FStar_Unionfind.equivalent v1 v2 in
              if uu____5461
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5474 = occurs_univ v1 u3 in
              if uu____5474
              then
                let uu____5475 =
                  let uu____5476 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5477 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5476 uu____5477 in
                try_umax_components u11 u21 uu____5475
              else
                (let uu____5479 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5479)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5489 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5489
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
  let uu____5560 = bc1 in
  match uu____5560 with
  | (bs1,mk_cod1) ->
      let uu____5585 = bc2 in
      (match uu____5585 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____5632 = FStar_Util.first_N n1 bs in
             match uu____5632 with
             | (bs3,rest) ->
                 let uu____5646 = mk_cod rest in (bs3, uu____5646) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____5664 =
               let uu____5668 = mk_cod1 [] in (bs1, uu____5668) in
             let uu____5670 =
               let uu____5674 = mk_cod2 [] in (bs2, uu____5674) in
             (uu____5664, uu____5670)
           else
             if l1 > l2
             then
               (let uu____5696 = curry l2 bs1 mk_cod1 in
                let uu____5703 =
                  let uu____5707 = mk_cod2 [] in (bs2, uu____5707) in
                (uu____5696, uu____5703))
             else
               (let uu____5716 =
                  let uu____5720 = mk_cod1 [] in (bs1, uu____5720) in
                let uu____5722 = curry l1 bs2 mk_cod2 in
                (uu____5716, uu____5722)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5826 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____5826
       then
         let uu____5827 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____5827
       else ());
      (let uu____5829 = next_prob probs in
       match uu____5829 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_5842 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___152_5842.wl_deferred);
               ctr = (uu___152_5842.ctr);
               defer_ok = (uu___152_5842.defer_ok);
               smt_ok = (uu___152_5842.smt_ok);
               tcenv = (uu___152_5842.tcenv)
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
                  let uu____5849 = solve_flex_rigid_join env tp probs1 in
                  (match uu____5849 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____5853 = solve_rigid_flex_meet env tp probs1 in
                     match uu____5853 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____5857,uu____5858) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5867 ->
                let uu____5872 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5900  ->
                          match uu____5900 with
                          | (c,uu____5905,uu____5906) -> c < probs.ctr)) in
                (match uu____5872 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____5928 =
                            FStar_List.map
                              (fun uu____5934  ->
                                 match uu____5934 with
                                 | (uu____5940,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____5928
                      | uu____5943 ->
                          let uu____5948 =
                            let uu___153_5949 = probs in
                            let uu____5950 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____5959  ->
                                      match uu____5959 with
                                      | (uu____5963,uu____5964,y) -> y)) in
                            {
                              attempting = uu____5950;
                              wl_deferred = rest;
                              ctr = (uu___153_5949.ctr);
                              defer_ok = (uu___153_5949.defer_ok);
                              smt_ok = (uu___153_5949.smt_ok);
                              tcenv = (uu___153_5949.tcenv)
                            } in
                          solve env uu____5948))))
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
            let uu____5971 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____5971 with
            | USolved wl1 ->
                let uu____5973 = solve_prob orig None [] wl1 in
                solve env uu____5973
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
                  let uu____6007 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6007 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6010 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6018;
                  FStar_Syntax_Syntax.pos = uu____6019;
                  FStar_Syntax_Syntax.vars = uu____6020;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6023;
                  FStar_Syntax_Syntax.pos = uu____6024;
                  FStar_Syntax_Syntax.vars = uu____6025;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6041 -> USolved wl
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
            ((let uu____6049 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6049
              then
                let uu____6050 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6050 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6058 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6058
         then
           let uu____6059 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6059
         else ());
        (let uu____6061 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6061 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6103 = head_matches_delta env () t1 t2 in
               match uu____6103 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6125 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6151 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6160 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6161 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6160, uu____6161)
                          | None  ->
                              let uu____6164 = FStar_Syntax_Subst.compress t1 in
                              let uu____6165 = FStar_Syntax_Subst.compress t2 in
                              (uu____6164, uu____6165) in
                        (match uu____6151 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6187 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6187 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6210 =
                                    let uu____6216 =
                                      let uu____6219 =
                                        let uu____6222 =
                                          let uu____6223 =
                                            let uu____6228 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6228) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6223 in
                                        FStar_Syntax_Syntax.mk uu____6222 in
                                      uu____6219 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6241 =
                                      let uu____6243 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6243] in
                                    (uu____6216, uu____6241) in
                                  Some uu____6210
                              | (uu____6252,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6254)) ->
                                  let uu____6259 =
                                    let uu____6263 =
                                      let uu____6265 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6265] in
                                    (t11, uu____6263) in
                                  Some uu____6259
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6271),uu____6272) ->
                                  let uu____6277 =
                                    let uu____6281 =
                                      let uu____6283 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6283] in
                                    (t21, uu____6281) in
                                  Some uu____6277
                              | uu____6288 ->
                                  let uu____6291 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6291 with
                                   | (head1,uu____6306) ->
                                       let uu____6321 =
                                         let uu____6322 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6322.FStar_Syntax_Syntax.n in
                                       (match uu____6321 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6329;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6331;_}
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
                                        | uu____6340 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6349) ->
                  let uu____6362 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6371  ->
                            match uu___127_6371 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6376 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6376 with
                                      | (u',uu____6387) ->
                                          let uu____6402 =
                                            let uu____6403 = whnf env u' in
                                            uu____6403.FStar_Syntax_Syntax.n in
                                          (match uu____6402 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6407) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____6423 -> false))
                                 | uu____6424 -> false)
                            | uu____6426 -> false)) in
                  (match uu____6362 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6447 tps =
                         match uu____6447 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6474 =
                                    let uu____6479 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____6479 in
                                  (match uu____6474 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6498 -> None) in
                       let uu____6503 =
                         let uu____6508 =
                           let uu____6512 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____6512, []) in
                         make_lower_bound uu____6508 lower_bounds in
                       (match uu____6503 with
                        | None  ->
                            ((let uu____6519 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6519
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
                            ((let uu____6532 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6532
                              then
                                let wl' =
                                  let uu___154_6534 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_6534.wl_deferred);
                                    ctr = (uu___154_6534.ctr);
                                    defer_ok = (uu___154_6534.defer_ok);
                                    smt_ok = (uu___154_6534.smt_ok);
                                    tcenv = (uu___154_6534.tcenv)
                                  } in
                                let uu____6535 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6535
                              else ());
                             (let uu____6537 =
                                solve_t env eq_prob
                                  (let uu___155_6538 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_6538.wl_deferred);
                                     ctr = (uu___155_6538.ctr);
                                     defer_ok = (uu___155_6538.defer_ok);
                                     smt_ok = (uu___155_6538.smt_ok);
                                     tcenv = (uu___155_6538.tcenv)
                                   }) in
                              match uu____6537 with
                              | Success uu____6540 ->
                                  let wl1 =
                                    let uu___156_6542 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_6542.wl_deferred);
                                      ctr = (uu___156_6542.ctr);
                                      defer_ok = (uu___156_6542.defer_ok);
                                      smt_ok = (uu___156_6542.smt_ok);
                                      tcenv = (uu___156_6542.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____6544 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____6547 -> None))))
              | uu____6548 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6555 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6555
         then
           let uu____6556 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6556
         else ());
        (let uu____6558 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____6558 with
         | (u,args) ->
             let uu____6585 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____6585 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____6616 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____6616 with
                    | (h1,args1) ->
                        let uu____6644 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____6644 with
                         | (h2,uu____6657) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____6676 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____6676
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6689 =
                                          let uu____6691 =
                                            let uu____6692 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____6692 in
                                          [uu____6691] in
                                        Some uu____6689))
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
                                       (let uu____6714 =
                                          let uu____6716 =
                                            let uu____6717 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____6717 in
                                          [uu____6716] in
                                        Some uu____6714))
                                  else None
                              | uu____6725 -> None)) in
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
                             let uu____6791 =
                               let uu____6797 =
                                 let uu____6800 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____6800 in
                               (uu____6797, m1) in
                             Some uu____6791)
                    | (uu____6809,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6811)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6843),uu____6844) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____6875 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6909) ->
                       let uu____6922 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_6931  ->
                                 match uu___128_6931 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6936 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____6936 with
                                           | (u',uu____6947) ->
                                               let uu____6962 =
                                                 let uu____6963 = whnf env u' in
                                                 uu____6963.FStar_Syntax_Syntax.n in
                                               (match uu____6962 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6967) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____6983 -> false))
                                      | uu____6984 -> false)
                                 | uu____6986 -> false)) in
                       (match uu____6922 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7011 tps =
                              match uu____7011 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7052 =
                                         let uu____7059 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7059 in
                                       (match uu____7052 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7094 -> None) in
                            let uu____7101 =
                              let uu____7108 =
                                let uu____7114 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7114, []) in
                              make_upper_bound uu____7108 upper_bounds in
                            (match uu____7101 with
                             | None  ->
                                 ((let uu____7123 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7123
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
                                 ((let uu____7142 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7142
                                   then
                                     let wl' =
                                       let uu___157_7144 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7144.wl_deferred);
                                         ctr = (uu___157_7144.ctr);
                                         defer_ok = (uu___157_7144.defer_ok);
                                         smt_ok = (uu___157_7144.smt_ok);
                                         tcenv = (uu___157_7144.tcenv)
                                       } in
                                     let uu____7145 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7145
                                   else ());
                                  (let uu____7147 =
                                     solve_t env eq_prob
                                       (let uu___158_7148 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7148.wl_deferred);
                                          ctr = (uu___158_7148.ctr);
                                          defer_ok = (uu___158_7148.defer_ok);
                                          smt_ok = (uu___158_7148.smt_ok);
                                          tcenv = (uu___158_7148.tcenv)
                                        }) in
                                   match uu____7147 with
                                   | Success uu____7150 ->
                                       let wl1 =
                                         let uu___159_7152 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7152.wl_deferred);
                                           ctr = (uu___159_7152.ctr);
                                           defer_ok =
                                             (uu___159_7152.defer_ok);
                                           smt_ok = (uu___159_7152.smt_ok);
                                           tcenv = (uu___159_7152.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7154 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7157 -> None))))
                   | uu____7158 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7223 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7223
                      then
                        let uu____7224 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7224
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7256 = hd1 in
                      let uu____7257 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7256.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7256.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7257
                      } in
                    let hd21 =
                      let uu___161_7261 = hd2 in
                      let uu____7262 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7261.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7261.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7262
                      } in
                    let prob =
                      let uu____7266 =
                        let uu____7269 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7269 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7266 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7277 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7277 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7280 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7280 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7298 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst in
                           let uu____7301 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7298 uu____7301 in
                         ((let uu____7307 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7307
                           then
                             let uu____7308 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7309 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7308 uu____7309
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7324 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7330 = aux scope env [] bs1 bs2 in
              match uu____7330 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7346 = compress_tprob wl problem in
        solve_t' env uu____7346 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7379 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7379 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7396,uu____7397) ->
                   let may_relate head3 =
                     let uu____7412 =
                       let uu____7413 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7413.FStar_Syntax_Syntax.n in
                     match uu____7412 with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7419 -> false in
                   let uu____7420 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7420
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
                                let uu____7437 =
                                  let uu____7438 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7438 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7437 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7440 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____7440
                   else giveup env1 "head mismatch" orig
               | (uu____7442,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_7450 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_7450.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_7450.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_7450.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_7450.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_7450.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_7450.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_7450.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_7450.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7451,None ) ->
                   ((let uu____7458 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7458
                     then
                       let uu____7459 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____7460 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____7461 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____7462 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7459
                         uu____7460 uu____7461 uu____7462
                     else ());
                    (let uu____7464 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____7464 with
                     | (head11,args1) ->
                         let uu____7490 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____7490 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7530 =
                                  let uu____7531 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____7532 = args_to_string args1 in
                                  let uu____7533 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____7534 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7531 uu____7532 uu____7533
                                    uu____7534 in
                                giveup env1 uu____7530 orig
                              else
                                (let uu____7536 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7539 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____7539 = FStar_Syntax_Util.Equal) in
                                 if uu____7536
                                 then
                                   let uu____7540 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____7540 with
                                   | USolved wl2 ->
                                       let uu____7542 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____7542
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7546 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____7546 with
                                    | (base1,refinement1) ->
                                        let uu____7572 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____7572 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____7626 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____7626 with
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
                                                           (fun uu____7636 
                                                              ->
                                                              fun uu____7637 
                                                                ->
                                                                match 
                                                                  (uu____7636,
                                                                    uu____7637)
                                                                with
                                                                | ((a,uu____7647),
                                                                   (a',uu____7649))
                                                                    ->
                                                                    let uu____7654
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
                                                                    uu____7654)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____7660 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____7660 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____7664 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_7697 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_7697.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____7717 = p in
          match uu____7717 with
          | (((u,k),xs,c),ps,(h,uu____7728,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7777 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____7777 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____7791 = h gs_xs in
                     let uu____7792 =
                       let uu____7799 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____7799
                         (fun _0_51  -> Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____7791 uu____7792 in
                   ((let uu____7830 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7830
                     then
                       let uu____7831 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____7832 = FStar_Syntax_Print.comp_to_string c in
                       let uu____7833 = FStar_Syntax_Print.term_to_string im in
                       let uu____7834 = FStar_Syntax_Print.tag_of_term im in
                       let uu____7835 =
                         let uu____7836 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____7836
                           (FStar_String.concat ", ") in
                       let uu____7839 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____7831 uu____7832 uu____7833 uu____7834
                         uu____7835 uu____7839
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_7857 =
          match uu___129_7857 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____7886 = p in
          match uu____7886 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7944 = FStar_List.nth ps i in
              (match uu____7944 with
               | (pi,uu____7947) ->
                   let uu____7952 = FStar_List.nth xs i in
                   (match uu____7952 with
                    | (xi,uu____7959) ->
                        let rec gs k =
                          let uu____7968 = FStar_Syntax_Util.arrow_formals k in
                          match uu____7968 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8020)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8028 = new_uvar r xs k_a in
                                    (match uu____8028 with
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
                                         let uu____8047 = aux subst2 tl1 in
                                         (match uu____8047 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8062 =
                                                let uu____8064 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8064 :: gi_xs' in
                                              let uu____8065 =
                                                let uu____8067 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8067 :: gi_ps' in
                                              (uu____8062, uu____8065))) in
                              aux [] bs in
                        let uu____8070 =
                          let uu____8071 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8071 in
                        if uu____8070
                        then None
                        else
                          (let uu____8074 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8074 with
                           | (g_xs,uu____8081) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8088 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8093 =
                                   let uu____8100 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____8100
                                     (fun _0_53  -> Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____8088
                                   uu____8093 in
                               let sub1 =
                                 let uu____8131 =
                                   let uu____8134 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8141 =
                                     let uu____8144 =
                                       FStar_List.map
                                         (fun uu____8150  ->
                                            match uu____8150 with
                                            | (uu____8155,uu____8156,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8144 in
                                   mk_problem (p_scope orig) orig uu____8134
                                     (p_rel orig) uu____8141 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8131 in
                               ((let uu____8166 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8166
                                 then
                                   let uu____8167 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8168 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8167 uu____8168
                                 else ());
                                (let wl2 =
                                   let uu____8171 =
                                     let uu____8173 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1) in
                                     Some uu____8173 in
                                   solve_prob orig uu____8171
                                     [TERM (u, proj)] wl1 in
                                 let uu____8178 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8178))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8202 = lhs in
          match uu____8202 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8225 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8225 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8247 =
                        let uu____8273 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8273) in
                      Some uu____8247
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8356 =
                           let uu____8360 =
                             let uu____8361 = FStar_Syntax_Subst.compress k in
                             uu____8361.FStar_Syntax_Syntax.n in
                           (uu____8360, args) in
                         match uu____8356 with
                         | (uu____8368,[]) ->
                             let uu____8370 =
                               let uu____8376 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8376) in
                             Some uu____8370
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____8393 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8393 with
                              | (uv1,uv_args) ->
                                  let uu____8422 =
                                    let uu____8423 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8423.FStar_Syntax_Syntax.n in
                                  (match uu____8422 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8430) ->
                                       let uu____8443 =
                                         pat_vars env [] uv_args in
                                       (match uu____8443 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8457  ->
                                                      let uu____8458 =
                                                        let uu____8459 =
                                                          let uu____8460 =
                                                            let uu____8463 =
                                                              let uu____8464
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____8464
                                                                FStar_Pervasives.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8463 in
                                                          fst uu____8460 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8459 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8458)) in
                                            let c1 =
                                              let uu____8470 =
                                                let uu____8471 =
                                                  let uu____8474 =
                                                    let uu____8475 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8475
                                                      FStar_Pervasives.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8474 in
                                                fst uu____8471 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8470 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____8484 =
                                                let uu____8491 =
                                                  let uu____8497 =
                                                    let uu____8498 =
                                                      let uu____8501 =
                                                        let uu____8502 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____8502
                                                          FStar_Pervasives.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____8501 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____8498 in
                                                  FStar_Util.Inl uu____8497 in
                                                Some uu____8491 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8484 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____8525 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8530)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____8556 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____8556
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8575 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____8575 with
                                  | (args1,rest) ->
                                      let uu____8591 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____8591 with
                                       | (xs2,c2) ->
                                           let uu____8599 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____8599
                                             (fun uu____8610  ->
                                                match uu____8610 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____8632 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____8632 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____8678 =
                                        let uu____8681 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____8681 in
                                      FStar_All.pipe_right uu____8678
                                        (fun _0_57  -> Some _0_57))
                         | uu____8689 ->
                             let uu____8693 =
                               let uu____8694 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____8698 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____8699 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____8694 uu____8698 uu____8699 in
                             failwith uu____8693 in
                       let uu____8703 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____8703
                         (fun uu____8731  ->
                            match uu____8731 with
                            | (xs1,c1) ->
                                let uu____8759 =
                                  let uu____8782 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____8782) in
                                Some uu____8759)) in
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
                     let uu____8854 = imitate orig env wl1 st in
                     match uu____8854 with
                     | Failed uu____8859 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____8865 = project orig env wl1 i st in
                      match uu____8865 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____8883 = FStar_Syntax_Util.head_and_args t21 in
                match uu____8883 with
                | (hd1,uu____8894) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____8912 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____8915 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____8915
                         then true
                         else
                           ((let uu____8918 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____8918
                             then
                               let uu____8919 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____8919
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____8927 =
                    let uu____8930 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____8930 FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____8927 FStar_Syntax_Free.names in
                let uu____8961 = FStar_Util.set_is_empty fvs_hd in
                if uu____8961
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____8970 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____8970 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____8978 =
                            let uu____8979 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____8979 in
                          giveup_or_defer1 orig uu____8978
                        else
                          (let uu____8981 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____8981
                           then
                             let uu____8982 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____8982
                              then
                                let uu____8983 = subterms args_lhs in
                                imitate' orig env wl1 uu____8983
                              else
                                ((let uu____8987 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____8987
                                  then
                                    let uu____8988 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____8989 = names_to_string fvs1 in
                                    let uu____8990 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____8988 uu____8989 uu____8990
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____8995 ->
                                        let uu____8996 = sn_binders env vars in
                                        u_abs k_uv uu____8996 t21 in
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
                               (let uu____9005 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9005
                                then
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
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9008 uu____9009 uu____9010
                                    else ());
                                   (let uu____9012 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9012
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
                     (let uu____9023 =
                        let uu____9024 = FStar_Syntax_Free.names t1 in
                        check_head uu____9024 t2 in
                      if uu____9023
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9028 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9028
                          then
                            let uu____9029 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9029
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9032 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9032 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9074 =
               match uu____9074 with
               | (t,u,k,args) ->
                   let uu____9104 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9104 with
                    | (all_formals,uu____9115) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9207  ->
                                        match uu____9207 with
                                        | (x,imp) ->
                                            let uu____9214 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9214, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9222 = FStar_Syntax_Util.type_u () in
                                match uu____9222 with
                                | (t1,uu____9226) ->
                                    let uu____9227 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    fst uu____9227 in
                              let uu____9230 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9230 with
                               | (t',tm_u1) ->
                                   let uu____9237 = destruct_flex_t t' in
                                   (match uu____9237 with
                                    | (uu____9257,u1,k1,uu____9260) ->
                                        let sol =
                                          let uu____9288 =
                                            let uu____9293 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____9293) in
                                          TERM uu____9288 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9353 = pat_var_opt env pat_args hd1 in
                              (match uu____9353 with
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
                                              (fun uu____9382  ->
                                                 match uu____9382 with
                                                 | (x,uu____9386) ->
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
                                      let uu____9392 =
                                        let uu____9393 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____9393 in
                                      if uu____9392
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9397 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9397 formals1
                                           tl1)))
                          | uu____9403 -> failwith "Impossible" in
                        let uu____9414 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____9414 all_formals args) in
             let solve_both_pats wl1 uu____9462 uu____9463 r =
               match (uu____9462, uu____9463) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9617 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____9617
                   then
                     let uu____9621 = solve_prob orig None [] wl1 in
                     solve env uu____9621
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____9636 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____9636
                       then
                         let uu____9637 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____9638 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____9639 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____9640 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____9641 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9637 uu____9638 uu____9639 uu____9640
                           uu____9641
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____9683 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____9683 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____9691 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____9691 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____9721 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____9721 in
                                  let uu____9724 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____9724 k3)
                           else
                             (let uu____9727 =
                                let uu____9728 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____9729 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____9730 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____9728 uu____9729 uu____9730 in
                              failwith uu____9727) in
                       let uu____9731 =
                         let uu____9737 =
                           let uu____9745 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____9745 in
                         match uu____9737 with
                         | (bs,k1') ->
                             let uu____9763 =
                               let uu____9771 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____9771 in
                             (match uu____9763 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____9792 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____9792 in
                                  let uu____9797 =
                                    let uu____9800 =
                                      let uu____9801 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____9801.FStar_Syntax_Syntax.n in
                                    let uu____9804 =
                                      let uu____9805 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____9805.FStar_Syntax_Syntax.n in
                                    (uu____9800, uu____9804) in
                                  (match uu____9797 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____9813,uu____9814) ->
                                       (k1', [sub_prob])
                                   | (uu____9818,FStar_Syntax_Syntax.Tm_type
                                      uu____9819) -> (k2', [sub_prob])
                                   | uu____9823 ->
                                       let uu____9826 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____9826 with
                                        | (t,uu____9835) ->
                                            let uu____9836 = new_uvar r zs t in
                                            (match uu____9836 with
                                             | (k_zs,uu____9845) ->
                                                 let kprob =
                                                   let uu____9847 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____9847 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____9731 with
                       | (k_u',sub_probs) ->
                           let uu____9861 =
                             let uu____9869 =
                               let uu____9870 = new_uvar r zs k_u' in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____9870 in
                             let uu____9875 =
                               let uu____9878 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____9878 in
                             let uu____9881 =
                               let uu____9884 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____9884 in
                             (uu____9869, uu____9875, uu____9881) in
                           (match uu____9861 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____9903 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____9903 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____9927 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____9927
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____9934 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____9934 with
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
             let solve_one_pat uu____9986 uu____9987 =
               match (uu____9986, uu____9987) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10091 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10091
                     then
                       let uu____10092 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10093 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10092 uu____10093
                     else ());
                    (let uu____10095 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____10095
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10105  ->
                              fun uu____10106  ->
                                match (uu____10105, uu____10106) with
                                | ((a,uu____10116),(t21,uu____10118)) ->
                                    let uu____10123 =
                                      let uu____10126 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10126
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10123
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____10130 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10130 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10140 = occurs_check env wl (u1, k1) t21 in
                        match uu____10140 with
                        | (occurs_ok,uu____10149) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10154 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10154
                            then
                              let sol =
                                let uu____10156 =
                                  let uu____10161 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10161) in
                                TERM uu____10156 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10174 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10174
                               then
                                 let uu____10175 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10175 with
                                 | (sol,(uu____10189,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10199 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10199
                                       then
                                         let uu____10200 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10200
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10205 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10207 = lhs in
             match uu____10207 with
             | (t1,u1,k1,args1) ->
                 let uu____10212 = rhs in
                 (match uu____10212 with
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
                       | uu____10238 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10244 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10244 with
                              | (sol,uu____10251) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10254 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10254
                                    then
                                      let uu____10255 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10255
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10260 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10262 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10262
        then
          let uu____10263 = solve_prob orig None [] wl in
          solve env uu____10263
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10267 = FStar_Util.physical_equality t1 t2 in
           if uu____10267
           then
             let uu____10268 = solve_prob orig None [] wl in
             solve env uu____10268
           else
             ((let uu____10271 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10271
               then
                 let uu____10272 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10272
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
                   let mk_c c uu___130_10318 =
                     match uu___130_10318 with
                     | [] -> c
                     | bs ->
                         let uu____10332 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10332 in
                   let uu____10342 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10342 with
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
                                   let uu____10428 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____10428
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____10430 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____10430))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_10507 =
                     match uu___131_10507 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____10542 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____10542 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10625 =
                                   let uu____10628 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____10629 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____10628
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10629 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____10625))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10644 -> true
                     | uu____10659 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____10687 =
                     let uu____10698 = maybe_eta t1 in
                     let uu____10703 = maybe_eta t2 in
                     (uu____10698, uu____10703) in
                   (match uu____10687 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_10734 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_10734.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_10734.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_10734.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_10734.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_10734.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_10734.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_10734.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_10734.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10767 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____10767
                        then
                          let uu____10768 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____10768 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10773 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____10784,FStar_Syntax_Syntax.Tm_refine uu____10785) ->
                   let uu____10794 = as_refinement env wl t1 in
                   (match uu____10794 with
                    | (x1,phi1) ->
                        let uu____10799 = as_refinement env wl t2 in
                        (match uu____10799 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____10805 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____10805 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____10838 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____10838
                                 (guard_on_element wl problem x11) in
                             let fallback uu____10842 =
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
                                 let uu____10848 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____10848 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____10855 =
                                   let uu____10858 =
                                     let uu____10859 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____10859 :: (p_scope orig) in
                                   mk_problem uu____10858 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____10855 in
                               let uu____10862 =
                                 solve env1
                                   (let uu___165_10863 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_10863.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_10863.smt_ok);
                                      tcenv = (uu___165_10863.tcenv)
                                    }) in
                               (match uu____10862 with
                                | Failed uu____10867 -> fallback ()
                                | Success uu____10870 ->
                                    let guard =
                                      let uu____10874 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst in
                                      let uu____10877 =
                                        let uu____10878 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst in
                                        FStar_All.pipe_right uu____10878
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____10874
                                        uu____10877 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___166_10885 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_10885.attempting);
                                        wl_deferred =
                                          (uu___166_10885.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_10885.defer_ok);
                                        smt_ok = (uu___166_10885.smt_ok);
                                        tcenv = (uu___166_10885.tcenv)
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
                   let uu____10939 = destruct_flex_t t1 in
                   let uu____10940 = destruct_flex_t t2 in
                   flex_flex1 orig uu____10939 uu____10940
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
                   let uu____10956 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____10956 t2 wl
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
                     (let uu___167_11005 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_11005.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_11005.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_11005.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_11005.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_11005.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_11005.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_11005.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_11005.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_11005.FStar_TypeChecker_Common.rank)
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
                      let uu____11023 =
                        let uu____11024 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11024 in
                      if uu____11023
                      then
                        let uu____11025 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_11028 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_11028.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_11028.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_11028.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_11028.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_11028.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_11028.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_11028.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_11028.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_11028.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11029 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11025 uu____11029 t2
                          wl
                      else
                        (let uu____11034 = base_and_refinement env wl t2 in
                         match uu____11034 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____11064 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_11067 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_11067.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_11067.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_11067.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_11067.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_11067.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_11067.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_11067.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_11067.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_11067.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____11068 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____11064
                                    uu____11068 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_11083 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_11083.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_11083.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____11086 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____11086 in
                                  let guard =
                                    let uu____11094 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst in
                                    FStar_Syntax_Util.mk_conj uu____11094
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
                     (let uu____11116 = base_and_refinement env wl t1 in
                      match uu____11116 with
                      | (t_base,uu____11127) ->
                          solve_t env
                            (let uu___171_11142 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_11142.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_11142.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_11142.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_11142.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_11142.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_11142.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_11142.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_11142.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____11145,uu____11146) ->
                   let t21 =
                     let uu____11154 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____11154 in
                   solve_t env
                     (let uu___172_11167 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_11167.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_11167.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_11167.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_11167.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_11167.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_11167.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_11167.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_11167.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_11167.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11168,FStar_Syntax_Syntax.Tm_refine uu____11169) ->
                   let t11 =
                     let uu____11177 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____11177 in
                   solve_t env
                     (let uu___173_11190 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_11190.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_11190.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_11190.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_11190.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_11190.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_11190.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_11190.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_11190.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_11190.FStar_TypeChecker_Common.rank)
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
                     let uu____11220 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11220 FStar_Pervasives.fst in
                   let head2 =
                     let uu____11251 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11251 FStar_Pervasives.fst in
                   let uu____11279 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11279
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11288 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11288
                      then
                        let guard =
                          let uu____11295 =
                            let uu____11296 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____11296 = FStar_Syntax_Util.Equal in
                          if uu____11295
                          then None
                          else
                            (let uu____11299 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_68  -> Some _0_68)
                               uu____11299) in
                        let uu____11301 = solve_prob orig guard [] wl in
                        solve env uu____11301
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____11305,uu____11306),uu____11307) ->
                   solve_t' env
                     (let uu___174_11336 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_11336.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_11336.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_11336.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_11336.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_11336.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_11336.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_11336.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_11336.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_11336.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11339,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____11341,uu____11342)) ->
                   solve_t' env
                     (let uu___175_11371 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_11371.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_11371.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_11371.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_11371.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_11371.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_11371.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_11371.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_11371.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_11371.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   let uu____11384 =
                     let uu____11385 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____11386 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____11385
                       uu____11386 in
                   failwith uu____11384
               | uu____11387 -> giveup env "head tag mismatch" orig)))
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
          (let uu____11419 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____11419
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____11427  ->
                  fun uu____11428  ->
                    match (uu____11427, uu____11428) with
                    | ((a1,uu____11438),(a2,uu____11440)) ->
                        let uu____11445 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_69  -> FStar_TypeChecker_Common.TProb _0_69)
                          uu____11445)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____11451 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____11451 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____11471 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____11478)::[] -> wp1
              | uu____11491 ->
                  let uu____11497 =
                    let uu____11498 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____11498 in
                  failwith uu____11497 in
            let uu____11501 =
              let uu____11507 =
                let uu____11508 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____11508 in
              [uu____11507] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____11501;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____11509 = lift_c1 () in solve_eq uu____11509 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_11513  ->
                       match uu___132_11513 with
                       | FStar_Syntax_Syntax.TOTAL 
                         |FStar_Syntax_Syntax.MLEFFECT 
                          |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____11514 -> false)) in
             let uu____11515 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____11539)::uu____11540,(wp2,uu____11542)::uu____11543)
                   -> (wp1, wp2)
               | uu____11584 ->
                   let uu____11597 =
                     let uu____11598 =
                       let uu____11601 =
                         let uu____11602 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____11603 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____11602 uu____11603 in
                       (uu____11601, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____11598 in
                   raise uu____11597 in
             match uu____11515 with
             | (wpc1,wpc2) ->
                 let uu____11620 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____11620
                 then
                   let uu____11623 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____11623 wl
                 else
                   (let uu____11627 =
                      let uu____11631 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____11631 in
                    match uu____11627 with
                    | (c2_decl,qualifiers) ->
                        let uu____11643 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____11643
                        then
                          let c1_repr =
                            let uu____11646 =
                              let uu____11647 =
                                let uu____11648 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____11648 in
                              let uu____11649 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____11647 uu____11649 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____11646 in
                          let c2_repr =
                            let uu____11651 =
                              let uu____11652 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____11653 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____11652 uu____11653 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____11651 in
                          let prob =
                            let uu____11655 =
                              let uu____11658 =
                                let uu____11659 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____11660 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____11659
                                  uu____11660 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____11658 in
                            FStar_TypeChecker_Common.TProb uu____11655 in
                          let wl1 =
                            let uu____11662 =
                              let uu____11664 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst in
                              Some uu____11664 in
                            solve_prob orig uu____11662 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____11671 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____11671
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____11673 =
                                     let uu____11676 =
                                       let uu____11677 =
                                         let uu____11687 =
                                           let uu____11688 =
                                             let uu____11689 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____11689] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____11688 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____11690 =
                                           let uu____11692 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____11693 =
                                             let uu____11695 =
                                               let uu____11696 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____11696 in
                                             [uu____11695] in
                                           uu____11692 :: uu____11693 in
                                         (uu____11687, uu____11690) in
                                       FStar_Syntax_Syntax.Tm_app uu____11677 in
                                     FStar_Syntax_Syntax.mk uu____11676 in
                                   uu____11673
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____11707 =
                                    let uu____11710 =
                                      let uu____11711 =
                                        let uu____11721 =
                                          let uu____11722 =
                                            let uu____11723 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____11723] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____11722 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____11724 =
                                          let uu____11726 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____11727 =
                                            let uu____11729 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____11730 =
                                              let uu____11732 =
                                                let uu____11733 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____11733 in
                                              [uu____11732] in
                                            uu____11729 :: uu____11730 in
                                          uu____11726 :: uu____11727 in
                                        (uu____11721, uu____11724) in
                                      FStar_Syntax_Syntax.Tm_app uu____11711 in
                                    FStar_Syntax_Syntax.mk uu____11710 in
                                  uu____11707
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____11744 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_70  ->
                                  FStar_TypeChecker_Common.TProb _0_70)
                               uu____11744 in
                           let wl1 =
                             let uu____11750 =
                               let uu____11752 =
                                 let uu____11755 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst in
                                 FStar_Syntax_Util.mk_conj uu____11755 g in
                               FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                                 uu____11752 in
                             solve_prob orig uu____11750 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____11765 = FStar_Util.physical_equality c1 c2 in
        if uu____11765
        then
          let uu____11766 = solve_prob orig None [] wl in
          solve env uu____11766
        else
          ((let uu____11769 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____11769
            then
              let uu____11770 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____11771 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____11770
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____11771
            else ());
           (let uu____11773 =
              let uu____11776 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____11777 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____11776, uu____11777) in
            match uu____11773 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____11781),FStar_Syntax_Syntax.Total
                    (t2,uu____11783)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____11796 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11796 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____11799,FStar_Syntax_Syntax.Total uu____11800) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let uu____11849 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11849 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let uu____11856 =
                       let uu___176_11859 = problem in
                       let uu____11862 =
                         let uu____11863 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11863 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_11859.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11862;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_11859.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_11859.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_11859.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_11859.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_11859.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_11859.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_11859.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_11859.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11856 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let uu____11868 =
                       let uu___177_11871 = problem in
                       let uu____11874 =
                         let uu____11875 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11875 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_11871.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_11871.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_11871.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11874;
                         FStar_TypeChecker_Common.element =
                           (uu___177_11871.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_11871.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_11871.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_11871.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_11871.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_11871.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11868 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____11876,FStar_Syntax_Syntax.Comp uu____11877) ->
                     let uu____11878 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____11878
                     then
                       let uu____11879 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____11879 wl
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
                           (let uu____11889 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____11889
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____11891 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____11891 with
                            | None  ->
                                let uu____11893 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____11894 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____11894) in
                                if uu____11893
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
                                  (let uu____11897 =
                                     let uu____11898 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____11899 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____11898 uu____11899 in
                                   giveup env uu____11897 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11904 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____11924  ->
              match uu____11924 with
              | (uu____11935,uu____11936,u,uu____11938,uu____11939,uu____11940)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____11904 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11969 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____11969 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____11979 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____11991  ->
                match uu____11991 with
                | (u1,u2) ->
                    let uu____11996 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____11997 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____11996 uu____11997)) in
      FStar_All.pipe_right uu____11979 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____12009,[])) -> "{}"
      | uu____12022 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____12032 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____12032
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____12035 =
              FStar_List.map
                (fun uu____12039  ->
                   match uu____12039 with
                   | (uu____12042,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____12035 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____12046 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____12046 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____12084 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____12084
    then
      let uu____12085 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____12086 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____12085
        (rel_to_string rel) uu____12086
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
            let uu____12106 =
              let uu____12108 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_72  -> Some _0_72) uu____12108 in
            FStar_Syntax_Syntax.new_bv uu____12106 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____12114 =
              let uu____12116 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_73  -> Some _0_73) uu____12116 in
            let uu____12118 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____12114 uu____12118 in
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
          let uu____12141 = FStar_Options.eager_inference () in
          if uu____12141
          then
            let uu___178_12142 = probs in
            {
              attempting = (uu___178_12142.attempting);
              wl_deferred = (uu___178_12142.wl_deferred);
              ctr = (uu___178_12142.ctr);
              defer_ok = false;
              smt_ok = (uu___178_12142.smt_ok);
              tcenv = (uu___178_12142.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____12153 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____12153
              then
                let uu____12154 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____12154
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
          ((let uu____12164 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____12164
            then
              let uu____12165 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____12165
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____12169 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____12169
             then
               let uu____12170 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____12170
             else ());
            (let f2 =
               let uu____12173 =
                 let uu____12174 = FStar_Syntax_Util.unmeta f1 in
                 uu____12174.FStar_Syntax_Syntax.n in
               match uu____12173 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____12178 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_12179 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_12179.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_12179.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_12179.FStar_TypeChecker_Env.implicits)
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
            let uu____12194 =
              let uu____12195 =
                let uu____12196 =
                  let uu____12197 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
                  FStar_All.pipe_right uu____12197
                    (fun _0_74  -> FStar_TypeChecker_Common.NonTrivial _0_74) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____12196;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____12195 in
            FStar_All.pipe_left (fun _0_75  -> Some _0_75) uu____12194
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____12230 =
        let uu____12231 =
          let uu____12232 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst in
          FStar_All.pipe_right uu____12232
            (fun _0_76  -> FStar_TypeChecker_Common.NonTrivial _0_76) in
        {
          FStar_TypeChecker_Env.guard_f = uu____12231;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      Some uu____12230
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
          (let uu____12258 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12258
           then
             let uu____12259 = FStar_Syntax_Print.term_to_string t1 in
             let uu____12260 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____12259
               uu____12260
           else ());
          (let prob =
             let uu____12263 =
               let uu____12266 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____12266 in
             FStar_All.pipe_left
               (fun _0_77  -> FStar_TypeChecker_Common.TProb _0_77)
               uu____12263 in
           let g =
             let uu____12271 =
               let uu____12273 = singleton' env prob smt_ok in
               solve_and_commit env uu____12273 (fun uu____12274  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____12271 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12288 = try_teq true env t1 t2 in
        match uu____12288 with
        | None  ->
            let uu____12290 =
              let uu____12291 =
                let uu____12294 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____12295 = FStar_TypeChecker_Env.get_range env in
                (uu____12294, uu____12295) in
              FStar_Errors.Error uu____12291 in
            raise uu____12290
        | Some g ->
            ((let uu____12298 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____12298
              then
                let uu____12299 = FStar_Syntax_Print.term_to_string t1 in
                let uu____12300 = FStar_Syntax_Print.term_to_string t2 in
                let uu____12301 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____12299
                  uu____12300 uu____12301
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
          (let uu____12317 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12317
           then
             let uu____12318 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____12319 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____12318
               uu____12319
           else ());
          (let uu____12321 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____12321 with
           | (prob,x) ->
               let g =
                 let uu____12329 =
                   let uu____12331 = singleton' env prob smt_ok in
                   solve_and_commit env uu____12331
                     (fun uu____12332  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____12329 in
               ((let uu____12338 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____12338
                 then
                   let uu____12339 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____12340 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____12341 =
                     let uu____12342 = FStar_Util.must g in
                     guard_to_string env uu____12342 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____12339 uu____12340 uu____12341
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
          let uu____12366 = FStar_TypeChecker_Env.get_range env in
          let uu____12367 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.err uu____12366 uu____12367
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____12379 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____12379
         then
           let uu____12380 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____12381 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____12380
             uu____12381
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____12386 =
             let uu____12389 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____12389 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_78  -> FStar_TypeChecker_Common.CProb _0_78) uu____12386 in
         let uu____12392 =
           let uu____12394 = singleton env prob in
           solve_and_commit env uu____12394 (fun uu____12395  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____12392)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____12414  ->
        match uu____12414 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____12439 =
                 let uu____12440 =
                   let uu____12443 =
                     let uu____12444 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____12445 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____12444 uu____12445 in
                   let uu____12446 = FStar_TypeChecker_Env.get_range env in
                   (uu____12443, uu____12446) in
                 FStar_Errors.Error uu____12440 in
               raise uu____12439) in
            let equiv v1 v' =
              let uu____12454 =
                let uu____12457 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____12458 = FStar_Syntax_Subst.compress_univ v' in
                (uu____12457, uu____12458) in
              match uu____12454 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____12466 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____12480 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____12480 with
                      | FStar_Syntax_Syntax.U_unif uu____12484 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____12495  ->
                                    match uu____12495 with
                                    | (u,v') ->
                                        let uu____12501 = equiv v1 v' in
                                        if uu____12501
                                        then
                                          let uu____12503 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____12503 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____12513 -> [])) in
            let uu____12516 =
              let wl =
                let uu___180_12519 = empty_worklist env in
                {
                  attempting = (uu___180_12519.attempting);
                  wl_deferred = (uu___180_12519.wl_deferred);
                  ctr = (uu___180_12519.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_12519.smt_ok);
                  tcenv = (uu___180_12519.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____12526  ->
                      match uu____12526 with
                      | (lb,v1) ->
                          let uu____12531 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____12531 with
                           | USolved wl1 -> ()
                           | uu____12533 -> fail lb v1))) in
            let rec check_ineq uu____12539 =
              match uu____12539 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____12546) -> true
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
                   | (FStar_Syntax_Syntax.U_max us,uu____12562) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12566,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____12571 -> false) in
            let uu____12574 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____12580  ->
                      match uu____12580 with
                      | (u,v1) ->
                          let uu____12585 = check_ineq (u, v1) in
                          if uu____12585
                          then true
                          else
                            ((let uu____12588 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____12588
                              then
                                let uu____12589 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____12590 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____12589
                                  uu____12590
                              else ());
                             false))) in
            if uu____12574
            then ()
            else
              ((let uu____12594 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____12594
                then
                  ((let uu____12596 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____12596);
                   FStar_Unionfind.rollback tx;
                   (let uu____12602 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____12602))
                else ());
               (let uu____12608 =
                  let uu____12609 =
                    let uu____12612 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____12612) in
                  FStar_Errors.Error uu____12609 in
                raise uu____12608))
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
      let fail uu____12645 =
        match uu____12645 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____12655 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____12655
       then
         let uu____12656 = wl_to_string wl in
         let uu____12657 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____12656 uu____12657
       else ());
      (let g1 =
         let uu____12669 = solve_and_commit env wl fail in
         match uu____12669 with
         | Some [] ->
             let uu___181_12676 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_12676.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_12676.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_12676.FStar_TypeChecker_Env.implicits)
             }
         | uu____12679 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_12682 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_12682.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_12682.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_12682.FStar_TypeChecker_Env.implicits)
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
            let uu___183_12708 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_12708.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_12708.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_12708.FStar_TypeChecker_Env.implicits)
            } in
          let uu____12709 =
            let uu____12710 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____12710 in
          if uu____12709
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____12716 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____12716
                   then
                     let uu____12717 = FStar_TypeChecker_Env.get_range env in
                     let uu____12718 =
                       let uu____12719 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____12719 in
                     FStar_Errors.diag uu____12717 uu____12718
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
                         ((let uu____12728 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____12728
                           then
                             let uu____12729 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____12730 =
                               let uu____12731 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____12731 in
                             FStar_Errors.diag uu____12729 uu____12730
                           else ());
                          (let vcs =
                             let uu____12737 = FStar_Options.use_tactics () in
                             if uu____12737
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____12751  ->
                                   match uu____12751 with
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
      let uu____12762 = discharge_guard' None env g true in
      match uu____12762 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____12782 = FStar_Unionfind.find u in
      match uu____12782 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____12791 -> false in
    let rec until_fixpoint acc implicits =
      let uu____12806 = acc in
      match uu____12806 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____12852 = hd1 in
               (match uu____12852 with
                | (uu____12859,env,u,tm,k,r) ->
                    let uu____12865 = unresolved u in
                    if uu____12865
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____12883 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____12883
                        then
                          let uu____12884 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____12888 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____12889 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____12884 uu____12888 uu____12889
                        else ());
                       (let uu____12891 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_12895 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_12895.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_12895.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_12895.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_12895.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_12895.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_12895.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_12895.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_12895.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_12895.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_12895.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_12895.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_12895.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_12895.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_12895.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_12895.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_12895.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_12895.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_12895.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_12895.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_12895.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_12895.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_12895.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_12895.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____12891 with
                        | (uu____12896,uu____12897,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_12900 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_12900.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_12900.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_12900.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____12903 =
                                discharge_guard'
                                  (Some
                                     (fun uu____12907  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____12903 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_12922 = g in
    let uu____12923 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_12922.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_12922.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_12922.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12923
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____12951 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____12951 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____12958 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____12958
      | (reason,uu____12960,uu____12961,e,t,r)::uu____12965 ->
          let uu____12979 =
            let uu____12980 = FStar_Syntax_Print.term_to_string t in
            let uu____12981 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____12980 uu____12981 reason in
          FStar_Errors.err r uu____12979
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_12988 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_12988.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_12988.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_12988.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____13006 = try_teq false env t1 t2 in
        match uu____13006 with
        | None  -> false
        | Some g ->
            let uu____13009 = discharge_guard' None env g false in
            (match uu____13009 with
             | Some uu____13013 -> true
             | None  -> false)