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
            let uu___131_64 = g1 in
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
                (uu___131_64.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___131_64.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___131_64.FStar_TypeChecker_Env.implicits)
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
          let uu___132_104 = g in
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
              (uu___132_104.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___132_104.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___132_104.FStar_TypeChecker_Env.implicits)
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
          let uu___133_145 = g in
          let uu____146 =
            let uu____147 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____147 in
          {
            FStar_TypeChecker_Env.guard_f = uu____146;
            FStar_TypeChecker_Env.deferred =
              (uu___133_145.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___133_145.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___133_145.FStar_TypeChecker_Env.implicits)
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
            let uu___134_250 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___134_250.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___134_250.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___134_250.FStar_TypeChecker_Env.implicits)
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
            let uu___135_277 = g in
            let uu____278 =
              let uu____279 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____279 in
            {
              FStar_TypeChecker_Env.guard_f = uu____278;
              FStar_TypeChecker_Env.deferred =
                (uu___135_277.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_277.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_277.FStar_TypeChecker_Env.implicits)
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
  fun uu___103_579  ->
    match uu___103_579 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____592 =
    let uu____593 = FStar_Syntax_Subst.compress t in
    uu____593.FStar_Syntax_Syntax.n in
  match uu____592 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____610 = FStar_Syntax_Print.uvar_to_string u in
      let uu____614 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____610 uu____614
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____617;
         FStar_Syntax_Syntax.pos = uu____618;
         FStar_Syntax_Syntax.vars = uu____619;_},args)
      ->
      let uu____647 = FStar_Syntax_Print.uvar_to_string u in
      let uu____651 = FStar_Syntax_Print.term_to_string ty in
      let uu____652 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____647 uu____651 uu____652
  | uu____653 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___104_659  ->
      match uu___104_659 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____663 =
            let uu____665 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____666 =
              let uu____668 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____669 =
                let uu____671 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____672 =
                  let uu____674 =
                    let uu____676 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____677 =
                      let uu____679 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____680 =
                        let uu____682 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____683 =
                          let uu____685 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____685] in
                        uu____682 :: uu____683 in
                      uu____679 :: uu____680 in
                    uu____676 :: uu____677 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____674 in
                uu____671 :: uu____672 in
              uu____668 :: uu____669 in
            uu____665 :: uu____666 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____663
      | FStar_TypeChecker_Common.CProb p ->
          let uu____690 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____691 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____690
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____691
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___105_697  ->
      match uu___105_697 with
      | UNIV (u,t) ->
          let x =
            let uu____701 = FStar_Options.hide_uvar_nums () in
            if uu____701
            then "?"
            else
              (let uu____703 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____703 FStar_Util.string_of_int) in
          let uu____705 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____705
      | TERM ((u,uu____707),t) ->
          let x =
            let uu____712 = FStar_Options.hide_uvar_nums () in
            if uu____712
            then "?"
            else
              (let uu____714 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____714 FStar_Util.string_of_int) in
          let uu____718 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____718
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____727 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____727 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____735 =
      let uu____737 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____737
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____735 (FStar_String.concat ", ")
let args_to_string args =
  let uu____755 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____763  ->
            match uu____763 with
            | (x,uu____767) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____755 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____772 =
      let uu____773 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____773 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____772;
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
        let uu___136_786 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___136_786.wl_deferred);
          ctr = (uu___136_786.ctr);
          defer_ok = (uu___136_786.defer_ok);
          smt_ok;
          tcenv = (uu___136_786.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___137_811 = empty_worklist env in
  let uu____812 = FStar_List.map Prims.snd g in
  {
    attempting = uu____812;
    wl_deferred = (uu___137_811.wl_deferred);
    ctr = (uu___137_811.ctr);
    defer_ok = false;
    smt_ok = (uu___137_811.smt_ok);
    tcenv = (uu___137_811.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___138_824 = wl in
        {
          attempting = (uu___138_824.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___138_824.ctr);
          defer_ok = (uu___138_824.defer_ok);
          smt_ok = (uu___138_824.smt_ok);
          tcenv = (uu___138_824.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___139_836 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___139_836.wl_deferred);
        ctr = (uu___139_836.ctr);
        defer_ok = (uu___139_836.defer_ok);
        smt_ok = (uu___139_836.smt_ok);
        tcenv = (uu___139_836.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____847 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____847
         then
           let uu____848 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____848
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___106_852  ->
    match uu___106_852 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___140_868 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___140_868.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___140_868.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___140_868.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___140_868.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___140_868.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___140_868.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___140_868.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___107_889  ->
    match uu___107_889 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_31  -> FStar_TypeChecker_Common.TProb _0_31)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.CProb _0_32)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___108_905  ->
      match uu___108_905 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___109_908  ->
    match uu___109_908 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___110_917  ->
    match uu___110_917 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___111_927  ->
    match uu___111_927 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___112_937  ->
    match uu___112_937 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___113_948  ->
    match uu___113_948 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___114_959  ->
    match uu___114_959 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___115_968  ->
    match uu___115_968 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_33  -> FStar_TypeChecker_Common.TProb _0_33) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.CProb _0_34) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____982 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____982 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____993  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1043 = next_pid () in
  let uu____1044 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1043;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1044;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1091 = next_pid () in
  let uu____1092 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1091;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1092;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1133 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1133;
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
        let uu____1185 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1185
        then
          let uu____1186 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1187 = prob_to_string env d in
          let uu____1188 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1186 uu____1187 uu____1188 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1193 -> failwith "impossible" in
           let uu____1194 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1202 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1203 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1202, uu____1203)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1207 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1208 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1207, uu____1208) in
           match uu____1194 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___116_1217  ->
            match uu___116_1217 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1224 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1227),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___117_1250  ->
           match uu___117_1250 with
           | UNIV uu____1252 -> None
           | TERM ((u,uu____1256),t) ->
               let uu____1260 = FStar_Unionfind.equivalent uv u in
               if uu____1260 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___118_1279  ->
           match uu___118_1279 with
           | UNIV (u',t) ->
               let uu____1283 = FStar_Unionfind.equivalent u u' in
               if uu____1283 then Some t else None
           | uu____1287 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1294 =
        let uu____1295 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1295 in
      FStar_Syntax_Subst.compress uu____1294
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1302 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1302
let norm_arg env t =
  let uu____1321 = sn env (Prims.fst t) in (uu____1321, (Prims.snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1338  ->
              match uu____1338 with
              | (x,imp) ->
                  let uu____1345 =
                    let uu___141_1346 = x in
                    let uu____1347 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___141_1346.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___141_1346.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1347
                    } in
                  (uu____1345, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1362 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1362
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1365 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1365
        | uu____1367 -> u2 in
      let uu____1368 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1368
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1475 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____1475 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1487;
               FStar_Syntax_Syntax.pos = uu____1488;
               FStar_Syntax_Syntax.vars = uu____1489;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1510 =
                 let uu____1511 = FStar_Syntax_Print.term_to_string tt in
                 let uu____1512 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1511
                   uu____1512 in
               failwith uu____1510)
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____1547 =
             let uu____1548 = FStar_Syntax_Subst.compress t1' in
             uu____1548.FStar_Syntax_Syntax.n in
           match uu____1547 with
           | FStar_Syntax_Syntax.Tm_refine uu____1560 -> aux true t1'
           | uu____1565 -> (t11, None))
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
        let uu____1600 =
          let uu____1601 = FStar_Syntax_Print.term_to_string t11 in
          let uu____1602 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1601
            uu____1602 in
        failwith uu____1600 in
  let uu____1612 = whnf env t1 in aux false uu____1612
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1621 =
        let uu____1631 = empty_worklist env in
        base_and_refinement env uu____1631 t in
      FStar_All.pipe_right uu____1621 Prims.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1655 = FStar_Syntax_Syntax.null_bv t in
    (uu____1655, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1675 = base_and_refinement env wl t in
  match uu____1675 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____1734 =
  match uu____1734 with
  | (t_base,refopt) ->
      let uu____1748 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____1748 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___119_1772  ->
      match uu___119_1772 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1776 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1777 =
            let uu____1778 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____1778 in
          let uu____1779 =
            let uu____1780 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____1780 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1776 uu____1777
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1779
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1784 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1785 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____1786 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1784 uu____1785
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1786
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____1790 =
      let uu____1792 =
        let uu____1794 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1804  ->
                  match uu____1804 with | (uu____1808,uu____1809,x) -> x)) in
        FStar_List.append wl.attempting uu____1794 in
      FStar_List.map (wl_prob_to_string wl) uu____1792 in
    FStar_All.pipe_right uu____1790 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1827 =
          let uu____1837 =
            let uu____1838 = FStar_Syntax_Subst.compress k in
            uu____1838.FStar_Syntax_Syntax.n in
          match uu____1837 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____1879 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____1879)
              else
                (let uu____1893 = FStar_Syntax_Util.abs_formals t in
                 match uu____1893 with
                 | (ys',t1,uu____1914) ->
                     let uu____1927 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____1927))
          | uu____1948 ->
              let uu____1949 =
                let uu____1955 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____1955) in
              ((ys, t), uu____1949) in
        match uu____1827 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2010 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____2010 c in
               let uu____2012 =
                 let uu____2019 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_35  -> FStar_Util.Inl _0_35) in
                 FStar_All.pipe_right uu____2019 (fun _0_36  -> Some _0_36) in
               FStar_Syntax_Util.abs ys1 t1 uu____2012)
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
            let uu____2070 = p_guard prob in
            match uu____2070 with
            | (uu____2073,uv) ->
                ((let uu____2076 =
                    let uu____2077 = FStar_Syntax_Subst.compress uv in
                    uu____2077.FStar_Syntax_Syntax.n in
                  match uu____2076 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____2097 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____2097
                        then
                          let uu____2098 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____2099 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____2100 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2098
                            uu____2099 uu____2100
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2104 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___142_2107 = wl in
                  {
                    attempting = (uu___142_2107.attempting);
                    wl_deferred = (uu___142_2107.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___142_2107.defer_ok);
                    smt_ok = (uu___142_2107.smt_ok);
                    tcenv = (uu___142_2107.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2120 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____2120
         then
           let uu____2121 = FStar_Util.string_of_int pid in
           let uu____2122 =
             let uu____2123 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____2123 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2121 uu____2122
         else ());
        commit sol;
        (let uu___143_2128 = wl in
         {
           attempting = (uu___143_2128.attempting);
           wl_deferred = (uu___143_2128.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___143_2128.defer_ok);
           smt_ok = (uu___143_2128.smt_ok);
           tcenv = (uu___143_2128.tcenv)
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
            | (uu____2157,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2165 = FStar_Syntax_Util.mk_conj t1 f in
                Some uu____2165 in
          (let uu____2171 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____2171
           then
             let uu____2172 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____2173 =
               let uu____2174 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____2174 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2172 uu____2173
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____2199 =
    let uu____2203 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____2203 FStar_Util.set_elements in
  FStar_All.pipe_right uu____2199
    (FStar_Util.for_some
       (fun uu____2224  ->
          match uu____2224 with
          | (uv,uu____2232) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2276 = occurs wl uk t in Prims.op_Negation uu____2276 in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2281 =
         let uu____2282 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk) in
         let uu____2286 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2282 uu____2286 in
       Some uu____2281) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____2334 = occurs_check env wl uk t in
  match uu____2334 with
  | (occurs_ok,msg) ->
      let uu____2351 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____2351, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set v1 in
  let uu____2415 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2439  ->
            fun uu____2440  ->
              match (uu____2439, uu____2440) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2483 =
                    let uu____2484 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____2484 in
                  if uu____2483
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2498 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2498
                     then
                       let uu____2505 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____2505)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____2415 with | (isect,uu____2527) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2576  ->
          fun uu____2577  ->
            match (uu____2576, uu____2577) with
            | ((a,uu____2587),(b,uu____2589)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (Prims.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2633 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2639  ->
                match uu____2639 with
                | (b,uu____2643) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2633 then None else Some (a, (Prims.snd hd1))
  | uu____2652 -> None
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
            let uu____2695 = pat_var_opt env seen hd1 in
            (match uu____2695 with
             | None  ->
                 ((let uu____2703 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2703
                   then
                     let uu____2704 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (Prims.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2704
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2716 =
      let uu____2717 = FStar_Syntax_Subst.compress t in
      uu____2717.FStar_Syntax_Syntax.n in
    match uu____2716 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2733 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2795;
         FStar_Syntax_Syntax.pos = uu____2796;
         FStar_Syntax_Syntax.vars = uu____2797;_},args)
      -> (t, uv, k, args)
  | uu____2838 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____2892 = destruct_flex_t t in
  match uu____2892 with
  | (t1,uv,k,args) ->
      let uu____2960 = pat_vars env [] args in
      (match uu____2960 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3016 -> ((t1, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option*
  FStar_Syntax_Syntax.delta_depth Prims.option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3064 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option*
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3087 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3091 -> false
let head_match: match_result -> match_result =
  fun uu___120_3094  ->
    match uu___120_3094 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3103 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3116 ->
          let uu____3117 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3117 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3127 -> fv.FStar_Syntax_Syntax.fv_delta)
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
          let uu____3195 = fv_delta_depth env fv in Some uu____3195
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
            let uu____3214 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____3214
            then FullMatch
            else
              (let uu____3216 =
                 let uu____3221 =
                   let uu____3223 = fv_delta_depth env f in Some uu____3223 in
                 let uu____3224 =
                   let uu____3226 = fv_delta_depth env g in Some uu____3226 in
                 (uu____3221, uu____3224) in
               MisMatch uu____3216)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3230),FStar_Syntax_Syntax.Tm_uinst (g,uu____3232)) ->
            let uu____3241 = head_matches env f g in
            FStar_All.pipe_right uu____3241 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3248),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3250)) ->
            let uu____3275 = FStar_Unionfind.equivalent uv uv' in
            if uu____3275 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3283),FStar_Syntax_Syntax.Tm_refine (y,uu____3285)) ->
            let uu____3294 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3294 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3296),uu____3297) ->
            let uu____3302 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____3302 head_match
        | (uu____3303,FStar_Syntax_Syntax.Tm_refine (x,uu____3305)) ->
            let uu____3310 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____3310 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3316),FStar_Syntax_Syntax.Tm_app (head',uu____3318))
            ->
            let uu____3347 = head_matches env head1 head' in
            FStar_All.pipe_right uu____3347 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3349),uu____3350) ->
            let uu____3365 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____3365 head_match
        | (uu____3366,FStar_Syntax_Syntax.Tm_app (head1,uu____3368)) ->
            let uu____3383 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____3383 head_match
        | uu____3384 ->
            let uu____3387 =
              let uu____3392 = delta_depth_of_term env t11 in
              let uu____3394 = delta_depth_of_term env t21 in
              (uu____3392, uu____3394) in
            MisMatch uu____3387
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3430 = FStar_Syntax_Util.head_and_args t in
    match uu____3430 with
    | (head1,uu____3442) ->
        let uu____3457 =
          let uu____3458 = FStar_Syntax_Util.un_uinst head1 in
          uu____3458.FStar_Syntax_Syntax.n in
        (match uu____3457 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3463 =
               let uu____3464 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____3464 FStar_Option.isSome in
             if uu____3463
             then
               let uu____3478 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____3478 (fun _0_37  -> Some _0_37)
             else None
         | uu____3481 -> None) in
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
          (let uu____3561 =
             let uu____3566 = maybe_inline t11 in
             let uu____3568 = maybe_inline t21 in (uu____3566, uu____3568) in
           match uu____3561 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3593 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____3593 with
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
        let uu____3608 =
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
             let uu____3616 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____3616)) in
        (match uu____3608 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3624 -> fail r
    | uu____3629 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3654 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3684 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3699 = FStar_Syntax_Util.type_u () in
      match uu____3699 with
      | (t,uu____3703) ->
          let uu____3704 = new_uvar r binders t in Prims.fst uu____3704
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3713 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____3713 Prims.fst
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
        let uu____3755 = head_matches env t1 t' in
        match uu____3755 with
        | MisMatch uu____3756 -> false
        | uu____3761 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3821,imp),T (t2,uu____3824)) -> (t2, imp)
                     | uu____3841 -> failwith "Bad reconstruction") args
                args' in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1)))
              None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3885  ->
                    match uu____3885 with
                    | (t2,uu____3893) ->
                        (None, INVARIANT, (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3926 = failwith "Bad reconstruction" in
          let uu____3927 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3927 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3980))::tcs2) ->
                       aux
                         (((let uu___144_4002 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_4002.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_4002.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4012 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___121_4043 =
                 match uu___121_4043 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let uu____4106 = decompose1 [] bs1 in
               (rebuild, matches, uu____4106))
      | uu____4134 ->
          let rebuild uu___122_4139 =
            match uu___122_4139 with
            | [] -> t1
            | uu____4141 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___123_4160  ->
    match uu___123_4160 with
    | T (t,uu____4162) -> t
    | uu____4171 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___124_4174  ->
    match uu___124_4174 with
    | T (t,uu____4176) -> FStar_Syntax_Syntax.as_arg t
    | uu____4185 -> failwith "Impossible"
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
              | (uu____4254,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____4273 = new_uvar r scope1 k in
                  (match uu____4273 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4285 ->
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_app (gi, args))) None
                               r in
                       let uu____4304 =
                         let uu____4305 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_38  ->
                              FStar_TypeChecker_Common.TProb _0_38)
                           uu____4305 in
                       ((T (gi_xs, mk_kind)), uu____4304))
              | (uu____4314,uu____4315,C uu____4316) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4403 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4414;
                         FStar_Syntax_Syntax.pos = uu____4415;
                         FStar_Syntax_Syntax.vars = uu____4416;_})
                        ->
                        let uu____4431 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4431 with
                         | (T (gi_xs,uu____4447),prob) ->
                             let uu____4457 =
                               let uu____4458 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_39  -> C _0_39)
                                 uu____4458 in
                             (uu____4457, [prob])
                         | uu____4460 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4470;
                         FStar_Syntax_Syntax.pos = uu____4471;
                         FStar_Syntax_Syntax.vars = uu____4472;_})
                        ->
                        let uu____4487 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____4487 with
                         | (T (gi_xs,uu____4503),prob) ->
                             let uu____4513 =
                               let uu____4514 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4514 in
                             (uu____4513, [prob])
                         | uu____4516 -> failwith "impossible")
                    | (uu____4522,uu____4523,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4525;
                         FStar_Syntax_Syntax.pos = uu____4526;
                         FStar_Syntax_Syntax.vars = uu____4527;_})
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
                        let uu____4601 =
                          let uu____4606 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____4606 FStar_List.unzip in
                        (match uu____4601 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____4635 =
                                 let uu____4636 =
                                   let uu____4639 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____4639 un_T in
                                 let uu____4640 =
                                   let uu____4646 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____4646
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____4636;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____4640;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____4635 in
                             ((C gi_xs), sub_probs))
                    | uu____4651 ->
                        let uu____4658 = sub_prob scope1 args q in
                        (match uu____4658 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____4403 with
                   | (tc,probs) ->
                       let uu____4676 =
                         match q with
                         | (Some b,uu____4702,uu____4703) ->
                             let uu____4711 =
                               let uu____4715 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____4715 :: args in
                             ((Some b), (b :: scope1), uu____4711)
                         | uu____4733 -> (None, scope1, args) in
                       (match uu____4676 with
                        | (bopt,scope2,args1) ->
                            let uu____4776 = aux scope2 args1 qs2 in
                            (match uu____4776 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____4797 =
                                         let uu____4799 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst)) in
                                         f :: uu____4799 in
                                       FStar_Syntax_Util.mk_conj_l uu____4797
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (Prims.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____4812 =
                                         let uu____4814 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (Prims.fst b) f in
                                         let uu____4815 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst)) in
                                         uu____4814 :: uu____4815 in
                                       FStar_Syntax_Util.mk_conj_l uu____4812 in
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
  let uu___145_4868 = p in
  let uu____4871 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____4872 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___145_4868.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4871;
    FStar_TypeChecker_Common.relation =
      (uu___145_4868.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4872;
    FStar_TypeChecker_Common.element =
      (uu___145_4868.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___145_4868.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___145_4868.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___145_4868.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___145_4868.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___145_4868.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____4882 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____4882
            (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
      | FStar_TypeChecker_Common.CProb uu____4887 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____4901 = compress_prob wl pr in
        FStar_All.pipe_right uu____4901 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4907 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____4907 with
           | (lh,uu____4920) ->
               let uu____4935 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____4935 with
                | (rh,uu____4948) ->
                    let uu____4963 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4972,FStar_Syntax_Syntax.Tm_uvar uu____4973)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____4998,uu____4999)
                          ->
                          let uu____5008 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____5008 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5048 ->
                                    let rank =
                                      let uu____5055 = is_top_level_prob prob in
                                      if uu____5055
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____5057 =
                                      let uu___146_5060 = tp in
                                      let uu____5063 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___146_5060.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___146_5060.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___146_5060.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5063;
                                        FStar_TypeChecker_Common.element =
                                          (uu___146_5060.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___146_5060.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___146_5060.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___146_5060.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___146_5060.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___146_5060.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____5057)))
                      | (uu____5073,FStar_Syntax_Syntax.Tm_uvar uu____5074)
                          ->
                          let uu____5083 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____5083 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5123 ->
                                    let uu____5129 =
                                      let uu___147_5134 = tp in
                                      let uu____5137 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___147_5134.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5137;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___147_5134.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___147_5134.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___147_5134.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___147_5134.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___147_5134.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___147_5134.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___147_5134.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___147_5134.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____5129)))
                      | (uu____5153,uu____5154) -> (rigid_rigid, tp) in
                    (match uu____4963 with
                     | (rank,tp1) ->
                         let uu____5165 =
                           FStar_All.pipe_right
                             (let uu___148_5168 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___148_5168.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___148_5168.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___148_5168.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___148_5168.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___148_5168.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___148_5168.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___148_5168.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___148_5168.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___148_5168.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.TProb _0_42) in
                         (rank, uu____5165))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5174 =
            FStar_All.pipe_right
              (let uu___149_5177 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___149_5177.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___149_5177.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___149_5177.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___149_5177.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___149_5177.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___149_5177.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___149_5177.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___149_5177.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___149_5177.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43) in
          (rigid_rigid, uu____5174)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option*
      FStar_TypeChecker_Common.prob Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____5209 probs =
      match uu____5209 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5239 = rank wl hd1 in
               (match uu____5239 with
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
    match projectee with | UDeferred _0 -> true | uu____5304 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5316 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5328 -> false
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
                        let uu____5365 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____5365 with
                        | (k,uu____5369) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5374 -> false)))
            | uu____5375 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5418 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____5418 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5421 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____5427 =
                     let uu____5428 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____5429 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5428
                       uu____5429 in
                   UFailed uu____5427)
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5446 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____5446 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____5449 ->
                let uu____5452 =
                  let uu____5453 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____5454 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5453
                    uu____5454 msg in
                UFailed uu____5452 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5461 =
                let uu____5462 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____5463 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5462 uu____5463 in
              failwith uu____5461
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5475 = FStar_Unionfind.equivalent v1 v2 in
              if uu____5475
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____5488 = occurs_univ v1 u3 in
              if uu____5488
              then
                let uu____5489 =
                  let uu____5490 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____5491 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5490 uu____5491 in
                try_umax_components u11 u21 uu____5489
              else
                (let uu____5493 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____5493)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____5503 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____5503
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
  let uu____5574 = bc1 in
  match uu____5574 with
  | (bs1,mk_cod1) ->
      let uu____5599 = bc2 in
      (match uu____5599 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____5646 = FStar_Util.first_N n1 bs in
             match uu____5646 with
             | (bs3,rest) ->
                 let uu____5660 = mk_cod rest in (bs3, uu____5660) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____5678 =
               let uu____5682 = mk_cod1 [] in (bs1, uu____5682) in
             let uu____5684 =
               let uu____5688 = mk_cod2 [] in (bs2, uu____5688) in
             (uu____5678, uu____5684)
           else
             if l1 > l2
             then
               (let uu____5710 = curry l2 bs1 mk_cod1 in
                let uu____5717 =
                  let uu____5721 = mk_cod2 [] in (bs2, uu____5721) in
                (uu____5710, uu____5717))
             else
               (let uu____5730 =
                  let uu____5734 = mk_cod1 [] in (bs1, uu____5734) in
                let uu____5736 = curry l1 bs2 mk_cod2 in
                (uu____5730, uu____5736)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5840 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____5840
       then
         let uu____5841 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____5841
       else ());
      (let uu____5843 = next_prob probs in
       match uu____5843 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___150_5856 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___150_5856.wl_deferred);
               ctr = (uu___150_5856.ctr);
               defer_ok = (uu___150_5856.defer_ok);
               smt_ok = (uu___150_5856.smt_ok);
               tcenv = (uu___150_5856.tcenv)
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
                  let uu____5863 = solve_flex_rigid_join env tp probs1 in
                  (match uu____5863 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____5867 = solve_rigid_flex_meet env tp probs1 in
                     match uu____5867 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____5871,uu____5872) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5881 ->
                let uu____5886 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5914  ->
                          match uu____5914 with
                          | (c,uu____5919,uu____5920) -> c < probs.ctr)) in
                (match uu____5886 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____5942 =
                            FStar_List.map
                              (fun uu____5948  ->
                                 match uu____5948 with
                                 | (uu____5954,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____5942
                      | uu____5957 ->
                          let uu____5962 =
                            let uu___151_5963 = probs in
                            let uu____5964 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____5973  ->
                                      match uu____5973 with
                                      | (uu____5977,uu____5978,y) -> y)) in
                            {
                              attempting = uu____5964;
                              wl_deferred = rest;
                              ctr = (uu___151_5963.ctr);
                              defer_ok = (uu___151_5963.defer_ok);
                              smt_ok = (uu___151_5963.smt_ok);
                              tcenv = (uu___151_5963.tcenv)
                            } in
                          solve env uu____5962))))
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
            let uu____5985 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____5985 with
            | USolved wl1 ->
                let uu____5987 = solve_prob orig None [] wl1 in
                solve env uu____5987
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
                  let uu____6021 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____6021 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6024 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6032;
                  FStar_Syntax_Syntax.pos = uu____6033;
                  FStar_Syntax_Syntax.vars = uu____6034;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6037;
                  FStar_Syntax_Syntax.pos = uu____6038;
                  FStar_Syntax_Syntax.vars = uu____6039;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6055 -> USolved wl
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
            ((let uu____6063 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____6063
              then
                let uu____6064 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6064 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6072 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6072
         then
           let uu____6073 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6073
         else ());
        (let uu____6075 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____6075 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6117 = head_matches_delta env () t1 t2 in
               match uu____6117 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6139 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6165 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6174 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____6175 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____6174, uu____6175)
                          | None  ->
                              let uu____6178 = FStar_Syntax_Subst.compress t1 in
                              let uu____6179 = FStar_Syntax_Subst.compress t2 in
                              (uu____6178, uu____6179) in
                        (match uu____6165 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6201 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_44  ->
                                    FStar_TypeChecker_Common.TProb _0_44)
                                 uu____6201 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6224 =
                                    let uu____6230 =
                                      let uu____6233 =
                                        let uu____6236 =
                                          let uu____6237 =
                                            let uu____6242 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____6242) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6237 in
                                        FStar_Syntax_Syntax.mk uu____6236 in
                                      uu____6233 None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____6255 =
                                      let uu____6257 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____6257] in
                                    (uu____6230, uu____6255) in
                                  Some uu____6224
                              | (uu____6266,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6268)) ->
                                  let uu____6273 =
                                    let uu____6277 =
                                      let uu____6279 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____6279] in
                                    (t11, uu____6277) in
                                  Some uu____6273
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6285),uu____6286) ->
                                  let uu____6291 =
                                    let uu____6295 =
                                      let uu____6297 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____6297] in
                                    (t21, uu____6295) in
                                  Some uu____6291
                              | uu____6302 ->
                                  let uu____6305 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____6305 with
                                   | (head1,uu____6320) ->
                                       let uu____6335 =
                                         let uu____6336 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____6336.FStar_Syntax_Syntax.n in
                                       (match uu____6335 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6343;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6345;_}
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
                                        | uu____6354 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6363) ->
                  let uu____6376 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___125_6385  ->
                            match uu___125_6385 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6390 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____6390 with
                                      | (u',uu____6401) ->
                                          let uu____6416 =
                                            let uu____6417 = whnf env u' in
                                            uu____6417.FStar_Syntax_Syntax.n in
                                          (match uu____6416 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6421) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____6437 -> false))
                                 | uu____6438 -> false)
                            | uu____6440 -> false)) in
                  (match uu____6376 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6461 tps =
                         match uu____6461 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6488 =
                                    let uu____6493 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____6493 in
                                  (match uu____6488 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6512 -> None) in
                       let uu____6517 =
                         let uu____6522 =
                           let uu____6526 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____6526, []) in
                         make_lower_bound uu____6522 lower_bounds in
                       (match uu____6517 with
                        | None  ->
                            ((let uu____6533 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6533
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
                            ((let uu____6546 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____6546
                              then
                                let wl' =
                                  let uu___152_6548 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___152_6548.wl_deferred);
                                    ctr = (uu___152_6548.ctr);
                                    defer_ok = (uu___152_6548.defer_ok);
                                    smt_ok = (uu___152_6548.smt_ok);
                                    tcenv = (uu___152_6548.tcenv)
                                  } in
                                let uu____6549 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6549
                              else ());
                             (let uu____6551 =
                                solve_t env eq_prob
                                  (let uu___153_6552 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___153_6552.wl_deferred);
                                     ctr = (uu___153_6552.ctr);
                                     defer_ok = (uu___153_6552.defer_ok);
                                     smt_ok = (uu___153_6552.smt_ok);
                                     tcenv = (uu___153_6552.tcenv)
                                   }) in
                              match uu____6551 with
                              | Success uu____6554 ->
                                  let wl1 =
                                    let uu___154_6556 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___154_6556.wl_deferred);
                                      ctr = (uu___154_6556.ctr);
                                      defer_ok = (uu___154_6556.defer_ok);
                                      smt_ok = (uu___154_6556.smt_ok);
                                      tcenv = (uu___154_6556.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1 in
                                  let uu____6558 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds in
                                  Some wl2
                              | uu____6561 -> None))))
              | uu____6562 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6569 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____6569
         then
           let uu____6570 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6570
         else ());
        (let uu____6572 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____6572 with
         | (u,args) ->
             let uu____6599 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____6599 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____6630 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____6630 with
                    | (h1,args1) ->
                        let uu____6658 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____6658 with
                         | (h2,uu____6671) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____6690 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____6690
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6703 =
                                          let uu____6705 =
                                            let uu____6706 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_45  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_45) uu____6706 in
                                          [uu____6705] in
                                        Some uu____6703))
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
                                       (let uu____6728 =
                                          let uu____6730 =
                                            let uu____6731 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____6731 in
                                          [uu____6730] in
                                        Some uu____6728))
                                  else None
                              | uu____6739 -> None)) in
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
                             let uu____6805 =
                               let uu____6811 =
                                 let uu____6814 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____6814 in
                               (uu____6811, m1) in
                             Some uu____6805)
                    | (uu____6823,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6825)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6857),uu____6858) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____6889 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6923) ->
                       let uu____6936 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___126_6945  ->
                                 match uu___126_6945 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6950 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____6950 with
                                           | (u',uu____6961) ->
                                               let uu____6976 =
                                                 let uu____6977 = whnf env u' in
                                                 uu____6977.FStar_Syntax_Syntax.n in
                                               (match uu____6976 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6981) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____6997 -> false))
                                      | uu____6998 -> false)
                                 | uu____7000 -> false)) in
                       (match uu____6936 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7025 tps =
                              match uu____7025 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7066 =
                                         let uu____7073 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____7073 in
                                       (match uu____7066 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7108 -> None) in
                            let uu____7115 =
                              let uu____7122 =
                                let uu____7128 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____7128, []) in
                              make_upper_bound uu____7122 upper_bounds in
                            (match uu____7115 with
                             | None  ->
                                 ((let uu____7137 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7137
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
                                 ((let uu____7156 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____7156
                                   then
                                     let wl' =
                                       let uu___155_7158 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___155_7158.wl_deferred);
                                         ctr = (uu___155_7158.ctr);
                                         defer_ok = (uu___155_7158.defer_ok);
                                         smt_ok = (uu___155_7158.smt_ok);
                                         tcenv = (uu___155_7158.tcenv)
                                       } in
                                     let uu____7159 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7159
                                   else ());
                                  (let uu____7161 =
                                     solve_t env eq_prob
                                       (let uu___156_7162 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___156_7162.wl_deferred);
                                          ctr = (uu___156_7162.ctr);
                                          defer_ok = (uu___156_7162.defer_ok);
                                          smt_ok = (uu___156_7162.smt_ok);
                                          tcenv = (uu___156_7162.tcenv)
                                        }) in
                                   match uu____7161 with
                                   | Success uu____7164 ->
                                       let wl1 =
                                         let uu___157_7166 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___157_7166.wl_deferred);
                                           ctr = (uu___157_7166.ctr);
                                           defer_ok =
                                             (uu___157_7166.defer_ok);
                                           smt_ok = (uu___157_7166.smt_ok);
                                           tcenv = (uu___157_7166.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1 in
                                       let uu____7168 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds in
                                       Some wl2
                                   | uu____7171 -> None))))
                   | uu____7172 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____7237 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____7237
                      then
                        let uu____7238 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7238
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___158_7270 = hd1 in
                      let uu____7271 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___158_7270.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___158_7270.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7271
                      } in
                    let hd21 =
                      let uu___159_7275 = hd2 in
                      let uu____7276 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___159_7275.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___159_7275.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7276
                      } in
                    let prob =
                      let uu____7280 =
                        let uu____7283 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7283 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_47  -> FStar_TypeChecker_Common.TProb _0_47)
                        uu____7280 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____7291 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7291 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____7294 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____7294 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7312 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst in
                           let uu____7315 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____7312 uu____7315 in
                         ((let uu____7321 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____7321
                           then
                             let uu____7322 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____7323 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7322 uu____7323
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7338 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____7344 = aux scope env [] bs1 bs2 in
              match uu____7344 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7360 = compress_tprob wl problem in
        solve_t' env uu____7360 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7393 = head_matches_delta env1 wl1 t1 t2 in
          match uu____7393 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7410,uu____7411) ->
                   let may_relate head3 =
                     let uu____7426 =
                       let uu____7427 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7427.FStar_Syntax_Syntax.n in
                     match uu____7426 with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7433 -> false in
                   let uu____7434 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____7434
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
                                let uu____7451 =
                                  let uu____7452 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7452 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____7451 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____7454 = solve_prob orig (Some guard) [] wl1 in
                     solve env1 uu____7454
                   else giveup env1 "head mismatch" orig
               | (uu____7456,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___160_7464 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___160_7464.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___160_7464.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___160_7464.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___160_7464.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___160_7464.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___160_7464.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___160_7464.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___160_7464.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7465,None ) ->
                   ((let uu____7472 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7472
                     then
                       let uu____7473 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____7474 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____7475 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____7476 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7473
                         uu____7474 uu____7475 uu____7476
                     else ());
                    (let uu____7478 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____7478 with
                     | (head11,args1) ->
                         let uu____7504 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____7504 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7544 =
                                  let uu____7545 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____7546 = args_to_string args1 in
                                  let uu____7547 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____7548 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7545 uu____7546 uu____7547
                                    uu____7548 in
                                giveup env1 uu____7544 orig
                              else
                                (let uu____7550 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7553 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____7553 = FStar_Syntax_Util.Equal) in
                                 if uu____7550
                                 then
                                   let uu____7554 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____7554 with
                                   | USolved wl2 ->
                                       let uu____7556 =
                                         solve_prob orig None [] wl2 in
                                       solve env1 uu____7556
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7560 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____7560 with
                                    | (base1,refinement1) ->
                                        let uu____7586 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____7586 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____7640 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____7640 with
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
                                                           (fun uu____7650 
                                                              ->
                                                              fun uu____7651 
                                                                ->
                                                                match 
                                                                  (uu____7650,
                                                                    uu____7651)
                                                                with
                                                                | ((a,uu____7661),
                                                                   (a',uu____7663))
                                                                    ->
                                                                    let uu____7668
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
                                                                    uu____7668)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____7674 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                Prims.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____7674 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____7678 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___161_7711 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___161_7711.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____7731 = p in
          match uu____7731 with
          | (((u,k),xs,c),ps,(h,uu____7742,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7791 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____7791 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____7805 = h gs_xs in
                     let uu____7806 =
                       let uu____7813 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_49  -> FStar_Util.Inl _0_49) in
                       FStar_All.pipe_right uu____7813
                         (fun _0_50  -> Some _0_50) in
                     FStar_Syntax_Util.abs xs1 uu____7805 uu____7806 in
                   ((let uu____7844 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____7844
                     then
                       let uu____7845 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____7846 = FStar_Syntax_Print.comp_to_string c in
                       let uu____7847 = FStar_Syntax_Print.term_to_string im in
                       let uu____7848 = FStar_Syntax_Print.tag_of_term im in
                       let uu____7849 =
                         let uu____7850 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____7850
                           (FStar_String.concat ", ") in
                       let uu____7853 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____7845 uu____7846 uu____7847 uu____7848
                         uu____7849 uu____7853
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___127_7871 =
          match uu___127_7871 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____7900 = p in
          match uu____7900 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____7958 = FStar_List.nth ps i in
              (match uu____7958 with
               | (pi,uu____7961) ->
                   let uu____7966 = FStar_List.nth xs i in
                   (match uu____7966 with
                    | (xi,uu____7973) ->
                        let rec gs k =
                          let uu____7982 = FStar_Syntax_Util.arrow_formals k in
                          match uu____7982 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8034)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____8042 = new_uvar r xs k_a in
                                    (match uu____8042 with
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
                                         let uu____8061 = aux subst2 tl1 in
                                         (match uu____8061 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8076 =
                                                let uu____8078 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____8078 :: gi_xs' in
                                              let uu____8079 =
                                                let uu____8081 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____8081 :: gi_ps' in
                                              (uu____8076, uu____8079))) in
                              aux [] bs in
                        let uu____8084 =
                          let uu____8085 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____8085 in
                        if uu____8084
                        then None
                        else
                          (let uu____8088 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____8088 with
                           | (g_xs,uu____8095) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____8102 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r in
                                 let uu____8107 =
                                   let uu____8114 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_51  -> FStar_Util.Inl _0_51) in
                                   FStar_All.pipe_right uu____8114
                                     (fun _0_52  -> Some _0_52) in
                                 FStar_Syntax_Util.abs xs uu____8102
                                   uu____8107 in
                               let sub1 =
                                 let uu____8145 =
                                   let uu____8148 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let uu____8155 =
                                     let uu____8158 =
                                       FStar_List.map
                                         (fun uu____8164  ->
                                            match uu____8164 with
                                            | (uu____8169,uu____8170,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h uu____8158 in
                                   mk_problem (p_scope orig) orig uu____8148
                                     (p_rel orig) uu____8155 None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_53  ->
                                      FStar_TypeChecker_Common.TProb _0_53)
                                   uu____8145 in
                               ((let uu____8180 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____8180
                                 then
                                   let uu____8181 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____8182 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8181 uu____8182
                                 else ());
                                (let wl2 =
                                   let uu____8185 =
                                     let uu____8187 =
                                       FStar_All.pipe_left Prims.fst
                                         (p_guard sub1) in
                                     Some uu____8187 in
                                   solve_prob orig uu____8185
                                     [TERM (u, proj)] wl1 in
                                 let uu____8192 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_54  -> Some _0_54) uu____8192))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8216 = lhs in
          match uu____8216 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8239 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____8239 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8261 =
                        let uu____8287 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____8287) in
                      Some uu____8261
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____8370 =
                           let uu____8374 =
                             let uu____8375 = FStar_Syntax_Subst.compress k in
                             uu____8375.FStar_Syntax_Syntax.n in
                           (uu____8374, args) in
                         match uu____8370 with
                         | (uu____8382,[]) ->
                             let uu____8384 =
                               let uu____8390 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____8390) in
                             Some uu____8384
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____8407 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____8407 with
                              | (uv1,uv_args) ->
                                  let uu____8436 =
                                    let uu____8437 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____8437.FStar_Syntax_Syntax.n in
                                  (match uu____8436 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8444) ->
                                       let uu____8457 =
                                         pat_vars env [] uv_args in
                                       (match uu____8457 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8471  ->
                                                      let uu____8472 =
                                                        let uu____8473 =
                                                          let uu____8474 =
                                                            let uu____8477 =
                                                              let uu____8478
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____8478
                                                                Prims.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8477 in
                                                          Prims.fst
                                                            uu____8474 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8473 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8472)) in
                                            let c1 =
                                              let uu____8484 =
                                                let uu____8485 =
                                                  let uu____8488 =
                                                    let uu____8489 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____8489 Prims.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8488 in
                                                Prims.fst uu____8485 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8484 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____8498 =
                                                let uu____8505 =
                                                  let uu____8511 =
                                                    let uu____8512 =
                                                      let uu____8515 =
                                                        let uu____8516 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____8516
                                                          Prims.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____8515 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____8512 in
                                                  FStar_Util.Inl uu____8511 in
                                                Some uu____8505 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8498 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____8539 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8544)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____8570 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____8570
                                 (fun _0_55  -> Some _0_55)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8589 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____8589 with
                                  | (args1,rest) ->
                                      let uu____8605 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____8605 with
                                       | (xs2,c2) ->
                                           let uu____8613 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____8613
                                             (fun uu____8624  ->
                                                match uu____8624 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____8646 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____8646 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____8692 =
                                        let uu____8695 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____8695 in
                                      FStar_All.pipe_right uu____8692
                                        (fun _0_56  -> Some _0_56))
                         | uu____8703 ->
                             let uu____8707 =
                               let uu____8708 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____8712 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____8713 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____8708 uu____8712 uu____8713 in
                             failwith uu____8707 in
                       let uu____8717 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____8717
                         (fun uu____8745  ->
                            match uu____8745 with
                            | (xs1,c1) ->
                                let uu____8773 =
                                  let uu____8796 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____8796) in
                                Some uu____8773)) in
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
                     let uu____8868 = imitate orig env wl1 st in
                     match uu____8868 with
                     | Failed uu____8873 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____8879 = project orig env wl1 i st in
                      match uu____8879 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____8897 = FStar_Syntax_Util.head_and_args t21 in
                match uu____8897 with
                | (hd1,uu____8908) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____8926 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____8929 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____8929
                         then true
                         else
                           ((let uu____8932 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____8932
                             then
                               let uu____8933 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____8933
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____8941 =
                    let uu____8944 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____8944 Prims.fst in
                  FStar_All.pipe_right uu____8941 FStar_Syntax_Free.names in
                let uu____8975 = FStar_Util.set_is_empty fvs_hd in
                if uu____8975
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____8984 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____8984 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____8992 =
                            let uu____8993 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____8993 in
                          giveup_or_defer1 orig uu____8992
                        else
                          (let uu____8995 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____8995
                           then
                             let uu____8996 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____8996
                              then
                                let uu____8997 = subterms args_lhs in
                                imitate' orig env wl1 uu____8997
                              else
                                ((let uu____9001 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____9001
                                  then
                                    let uu____9002 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____9003 = names_to_string fvs1 in
                                    let uu____9004 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9002 uu____9003 uu____9004
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9009 ->
                                        let uu____9010 = sn_binders env vars in
                                        u_abs k_uv uu____9010 t21 in
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
                               (let uu____9019 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____9019
                                then
                                  ((let uu____9021 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____9021
                                    then
                                      let uu____9022 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____9023 = names_to_string fvs1 in
                                      let uu____9024 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9022 uu____9023 uu____9024
                                    else ());
                                   (let uu____9026 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9026
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
                     (let uu____9037 =
                        let uu____9038 = FStar_Syntax_Free.names t1 in
                        check_head uu____9038 t2 in
                      if uu____9037
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____9042 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____9042
                          then
                            let uu____9043 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9043
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9046 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9046 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9088 =
               match uu____9088 with
               | (t,u,k,args) ->
                   let uu____9118 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____9118 with
                    | (all_formals,uu____9129) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9221  ->
                                        match uu____9221 with
                                        | (x,imp) ->
                                            let uu____9228 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____9228, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____9236 = FStar_Syntax_Util.type_u () in
                                match uu____9236 with
                                | (t1,uu____9240) ->
                                    let uu____9241 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    Prims.fst uu____9241 in
                              let uu____9244 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____9244 with
                               | (t',tm_u1) ->
                                   let uu____9251 = destruct_flex_t t' in
                                   (match uu____9251 with
                                    | (uu____9271,u1,k1,uu____9274) ->
                                        let sol =
                                          let uu____9302 =
                                            let uu____9307 =
                                              u_abs k all_formals t' in
                                            ((u, k), uu____9307) in
                                          TERM uu____9302 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9367 = pat_var_opt env pat_args hd1 in
                              (match uu____9367 with
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
                                              (fun uu____9396  ->
                                                 match uu____9396 with
                                                 | (x,uu____9400) ->
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
                                      let uu____9406 =
                                        let uu____9407 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____9407 in
                                      if uu____9406
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9411 =
                                           FStar_Util.set_add
                                             (Prims.fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9411 formals1
                                           tl1)))
                          | uu____9417 -> failwith "Impossible" in
                        let uu____9428 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____9428 all_formals args) in
             let solve_both_pats wl1 uu____9476 uu____9477 r =
               match (uu____9476, uu____9477) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9631 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____9631
                   then
                     let uu____9635 = solve_prob orig None [] wl1 in
                     solve env uu____9635
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____9650 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____9650
                       then
                         let uu____9651 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____9652 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____9653 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____9654 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____9655 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9651 uu____9652 uu____9653 uu____9654
                           uu____9655
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____9697 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____9697 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____9705 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____9705 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____9735 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____9735 in
                                  let uu____9738 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____9738 k3)
                           else
                             (let uu____9741 =
                                let uu____9742 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____9743 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____9744 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____9742 uu____9743 uu____9744 in
                              failwith uu____9741) in
                       let uu____9745 =
                         let uu____9751 =
                           let uu____9759 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____9759 in
                         match uu____9751 with
                         | (bs,k1') ->
                             let uu____9777 =
                               let uu____9785 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____9785 in
                             (match uu____9777 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____9806 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_57  ->
                                         FStar_TypeChecker_Common.TProb _0_57)
                                      uu____9806 in
                                  let uu____9811 =
                                    let uu____9814 =
                                      let uu____9815 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____9815.FStar_Syntax_Syntax.n in
                                    let uu____9818 =
                                      let uu____9819 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____9819.FStar_Syntax_Syntax.n in
                                    (uu____9814, uu____9818) in
                                  (match uu____9811 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____9827,uu____9828) ->
                                       (k1', [sub_prob])
                                   | (uu____9832,FStar_Syntax_Syntax.Tm_type
                                      uu____9833) -> (k2', [sub_prob])
                                   | uu____9837 ->
                                       let uu____9840 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____9840 with
                                        | (t,uu____9849) ->
                                            let uu____9850 = new_uvar r zs t in
                                            (match uu____9850 with
                                             | (k_zs,uu____9859) ->
                                                 let kprob =
                                                   let uu____9861 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_58  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_58) uu____9861 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____9745 with
                       | (k_u',sub_probs) ->
                           let uu____9875 =
                             let uu____9883 =
                               let uu____9884 = new_uvar r zs k_u' in
                               FStar_All.pipe_left Prims.fst uu____9884 in
                             let uu____9889 =
                               let uu____9892 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____9892 in
                             let uu____9895 =
                               let uu____9898 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____9898 in
                             (uu____9883, uu____9889, uu____9895) in
                           (match uu____9875 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____9917 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____9917 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____9941 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____9941
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____9948 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____9948 with
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
             let solve_one_pat uu____10000 uu____10001 =
               match (uu____10000, uu____10001) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10105 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____10105
                     then
                       let uu____10106 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____10107 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10106 uu____10107
                     else ());
                    (let uu____10109 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____10109
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10119  ->
                              fun uu____10120  ->
                                match (uu____10119, uu____10120) with
                                | ((a,uu____10130),(t21,uu____10132)) ->
                                    let uu____10137 =
                                      let uu____10140 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____10140
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____10137
                                      (fun _0_59  ->
                                         FStar_TypeChecker_Common.TProb _0_59))
                           xs args2 in
                       let guard =
                         let uu____10144 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p) Prims.fst)
                             sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____10144 in
                       let wl1 = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____10154 = occurs_check env wl (u1, k1) t21 in
                        match uu____10154 with
                        | (occurs_ok,uu____10163) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____10168 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____10168
                            then
                              let sol =
                                let uu____10170 =
                                  let uu____10175 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____10175) in
                                TERM uu____10170 in
                              let wl1 = solve_prob orig None [sol] wl in
                              solve env wl1
                            else
                              (let uu____10188 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____10188
                               then
                                 let uu____10189 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____10189 with
                                 | (sol,(uu____10203,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____10213 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____10213
                                       then
                                         let uu____10214 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10214
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10219 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____10221 = lhs in
             match uu____10221 with
             | (t1,u1,k1,args1) ->
                 let uu____10226 = rhs in
                 (match uu____10226 with
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
                       | uu____10252 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10258 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____10258 with
                              | (sol,uu____10265) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____10268 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____10268
                                    then
                                      let uu____10269 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10269
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10274 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____10276 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____10276
        then
          let uu____10277 = solve_prob orig None [] wl in
          solve env uu____10277
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____10281 = FStar_Util.physical_equality t1 t2 in
           if uu____10281
           then
             let uu____10282 = solve_prob orig None [] wl in
             solve env uu____10282
           else
             ((let uu____10285 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____10285
               then
                 let uu____10286 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____10286
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
                   let mk_c c uu___128_10332 =
                     match uu___128_10332 with
                     | [] -> c
                     | bs ->
                         let uu____10346 =
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))) None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____10346 in
                   let uu____10360 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____10360 with
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
                                   let uu____10446 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____10446
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____10448 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_TypeChecker_Common.CProb _0_60)
                                   uu____10448))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___129_10525 =
                     match uu___129_10525 with
                     | [] -> t
                     | bs ->
                         (FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____10564 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____10564 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10647 =
                                   let uu____10650 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____10651 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____10650
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10651 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____10647))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10666 -> true
                     | uu____10681 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____10709 =
                     let uu____10720 = maybe_eta t1 in
                     let uu____10725 = maybe_eta t2 in
                     (uu____10720, uu____10725) in
                   (match uu____10709 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___162_10756 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___162_10756.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___162_10756.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___162_10756.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___162_10756.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___162_10756.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___162_10756.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___162_10756.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___162_10756.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10789 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____10789
                        then
                          let uu____10790 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____10790 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10795 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____10806,FStar_Syntax_Syntax.Tm_refine uu____10807) ->
                   let uu____10816 = as_refinement env wl t1 in
                   (match uu____10816 with
                    | (x1,phi1) ->
                        let uu____10821 = as_refinement env wl t2 in
                        (match uu____10821 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____10827 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_62  ->
                                    FStar_TypeChecker_Common.TProb _0_62)
                                 uu____10827 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____10860 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____10860
                                 (guard_on_element wl problem x11) in
                             let fallback uu____10864 =
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
                                 let uu____10870 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst in
                                 FStar_Syntax_Util.mk_conj uu____10870 impl in
                               let wl1 = solve_prob orig (Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____10877 =
                                   let uu____10880 =
                                     let uu____10881 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____10881 :: (p_scope orig) in
                                   mk_problem uu____10880 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_TypeChecker_Common.TProb _0_63)
                                   uu____10877 in
                               let uu____10884 =
                                 solve env1
                                   (let uu___163_10885 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___163_10885.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___163_10885.smt_ok);
                                      tcenv = (uu___163_10885.tcenv)
                                    }) in
                               (match uu____10884 with
                                | Failed uu____10889 -> fallback ()
                                | Success uu____10892 ->
                                    let guard =
                                      let uu____10896 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob) Prims.fst in
                                      let uu____10899 =
                                        let uu____10900 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob) Prims.fst in
                                        FStar_All.pipe_right uu____10900
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____10896
                                        uu____10899 in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl2 =
                                      let uu___164_10907 = wl1 in
                                      {
                                        attempting =
                                          (uu___164_10907.attempting);
                                        wl_deferred =
                                          (uu___164_10907.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___164_10907.defer_ok);
                                        smt_ok = (uu___164_10907.smt_ok);
                                        tcenv = (uu___164_10907.tcenv)
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
                   let uu____10961 = destruct_flex_t t1 in
                   let uu____10962 = destruct_flex_t t2 in
                   flex_flex1 orig uu____10961 uu____10962
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
                   let uu____10978 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____10978 t2 wl
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
                     (let uu___165_11027 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___165_11027.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___165_11027.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___165_11027.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___165_11027.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___165_11027.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___165_11027.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___165_11027.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___165_11027.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___165_11027.FStar_TypeChecker_Common.rank)
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
                      let uu____11045 =
                        let uu____11046 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____11046 in
                      if uu____11045
                      then
                        let uu____11047 =
                          FStar_All.pipe_left
                            (fun _0_64  ->
                               FStar_TypeChecker_Common.TProb _0_64)
                            (let uu___166_11050 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_11050.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_11050.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_11050.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_11050.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_11050.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___166_11050.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_11050.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_11050.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_11050.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____11051 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____11047 uu____11051 t2
                          wl
                      else
                        (let uu____11056 = base_and_refinement env wl t2 in
                         match uu____11056 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____11086 =
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      (let uu___167_11089 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___167_11089.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___167_11089.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___167_11089.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___167_11089.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___167_11089.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___167_11089.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___167_11089.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___167_11089.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___167_11089.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____11090 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____11086
                                    uu____11090 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___168_11105 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___168_11105.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___168_11105.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____11108 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      uu____11108 in
                                  let guard =
                                    let uu____11116 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob) Prims.fst in
                                    FStar_Syntax_Util.mk_conj uu____11116
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
                     (let uu____11138 = base_and_refinement env wl t1 in
                      match uu____11138 with
                      | (t_base,uu____11149) ->
                          solve_t env
                            (let uu___169_11164 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_11164.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_11164.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_11164.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_11164.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___169_11164.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_11164.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_11164.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_11164.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____11167,uu____11168) ->
                   let t21 =
                     let uu____11176 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____11176 in
                   solve_t env
                     (let uu___170_11189 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___170_11189.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___170_11189.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___170_11189.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___170_11189.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___170_11189.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___170_11189.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___170_11189.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___170_11189.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___170_11189.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11190,FStar_Syntax_Syntax.Tm_refine uu____11191) ->
                   let t11 =
                     let uu____11199 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____11199 in
                   solve_t env
                     (let uu___171_11212 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___171_11212.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___171_11212.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___171_11212.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___171_11212.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___171_11212.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___171_11212.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___171_11212.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___171_11212.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___171_11212.FStar_TypeChecker_Common.rank)
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
                     let uu____11242 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____11242 Prims.fst in
                   let head2 =
                     let uu____11273 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____11273 Prims.fst in
                   let uu____11301 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____11301
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____11310 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____11310
                      then
                        let guard =
                          let uu____11317 =
                            let uu____11318 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____11318 = FStar_Syntax_Util.Equal in
                          if uu____11317
                          then None
                          else
                            (let uu____11321 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_67  -> Some _0_67)
                               uu____11321) in
                        let uu____11323 = solve_prob orig guard [] wl in
                        solve env uu____11323
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____11327,uu____11328),uu____11329) ->
                   solve_t' env
                     (let uu___172_11358 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_11358.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___172_11358.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___172_11358.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___172_11358.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_11358.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_11358.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_11358.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_11358.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_11358.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11361,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____11363,uu____11364)) ->
                   solve_t' env
                     (let uu___173_11393 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_11393.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___173_11393.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___173_11393.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___173_11393.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_11393.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_11393.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_11393.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_11393.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_11393.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   let uu____11406 =
                     let uu____11407 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____11408 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____11407
                       uu____11408 in
                   failwith uu____11406
               | uu____11409 -> giveup env "head tag mismatch" orig)))
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
          (let uu____11441 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____11441
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____11449  ->
                  fun uu____11450  ->
                    match (uu____11449, uu____11450) with
                    | ((a1,uu____11460),(a2,uu____11462)) ->
                        let uu____11467 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                          uu____11467)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____11473 =
               FStar_List.map
                 (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                 sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____11473 in
           let wl1 = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____11493 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____11500)::[] -> wp1
              | uu____11513 ->
                  let uu____11519 =
                    let uu____11520 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____11520 in
                  failwith uu____11519 in
            let uu____11523 =
              let uu____11529 =
                let uu____11530 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____11530 in
              [uu____11529] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____11523;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____11531 = lift_c1 () in solve_eq uu____11531 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___130_11535  ->
                       match uu___130_11535 with
                       | FStar_Syntax_Syntax.TOTAL 
                         |FStar_Syntax_Syntax.MLEFFECT 
                          |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____11536 -> false)) in
             let uu____11537 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____11561)::uu____11562,(wp2,uu____11564)::uu____11565)
                   -> (wp1, wp2)
               | uu____11606 ->
                   let uu____11619 =
                     let uu____11620 =
                       let uu____11623 =
                         let uu____11624 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____11625 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____11624 uu____11625 in
                       (uu____11623, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____11620 in
                   Prims.raise uu____11619 in
             match uu____11537 with
             | (wpc1,wpc2) ->
                 let uu____11642 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____11642
                 then
                   let uu____11645 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env uu____11645 wl
                 else
                   (let c2_decl =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c21.FStar_Syntax_Syntax.effect_name in
                    let uu____11650 =
                      FStar_All.pipe_right
                        c2_decl.FStar_Syntax_Syntax.qualifiers
                        (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                    if uu____11650
                    then
                      let c1_repr =
                        let uu____11653 =
                          let uu____11654 =
                            let uu____11655 = lift_c1 () in
                            FStar_Syntax_Syntax.mk_Comp uu____11655 in
                          let uu____11656 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c11.FStar_Syntax_Syntax.result_typ in
                          FStar_TypeChecker_Env.reify_comp env uu____11654
                            uu____11656 in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11653 in
                      let c2_repr =
                        let uu____11658 =
                          let uu____11659 = FStar_Syntax_Syntax.mk_Comp c21 in
                          let uu____11660 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c21.FStar_Syntax_Syntax.result_typ in
                          FStar_TypeChecker_Env.reify_comp env uu____11659
                            uu____11660 in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11658 in
                      let prob =
                        let uu____11662 =
                          let uu____11665 =
                            let uu____11666 =
                              FStar_Syntax_Print.term_to_string c1_repr in
                            let uu____11667 =
                              FStar_Syntax_Print.term_to_string c2_repr in
                            FStar_Util.format2 "sub effect repr: %s <: %s"
                              uu____11666 uu____11667 in
                          sub_prob c1_repr
                            problem.FStar_TypeChecker_Common.relation c2_repr
                            uu____11665 in
                        FStar_TypeChecker_Common.TProb uu____11662 in
                      let wl1 =
                        let uu____11669 =
                          let uu____11671 =
                            FStar_All.pipe_right (p_guard prob) Prims.fst in
                          Some uu____11671 in
                        solve_prob orig uu____11669 [] wl in
                      solve env (attempt [prob] wl1)
                    else
                      (let g =
                         if env.FStar_TypeChecker_Env.lax
                         then FStar_Syntax_Util.t_true
                         else
                           if is_null_wp_2
                           then
                             ((let uu____11678 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Rel") in
                               if uu____11678
                               then
                                 FStar_Util.print_string
                                   "Using trivial wp ... \n"
                               else ());
                              (let uu____11680 =
                                 let uu____11683 =
                                   let uu____11684 =
                                     let uu____11694 =
                                       let uu____11695 =
                                         let uu____11696 =
                                           env.FStar_TypeChecker_Env.universe_of
                                             env
                                             c11.FStar_Syntax_Syntax.result_typ in
                                         [uu____11696] in
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         uu____11695 env c2_decl
                                         c2_decl.FStar_Syntax_Syntax.trivial in
                                     let uu____11697 =
                                       let uu____11699 =
                                         FStar_Syntax_Syntax.as_arg
                                           c11.FStar_Syntax_Syntax.result_typ in
                                       let uu____11700 =
                                         let uu____11702 =
                                           let uu____11703 =
                                             (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                               c11.FStar_Syntax_Syntax.result_typ
                                               wpc1 in
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             uu____11703 in
                                         [uu____11702] in
                                       uu____11699 :: uu____11700 in
                                     (uu____11694, uu____11697) in
                                   FStar_Syntax_Syntax.Tm_app uu____11684 in
                                 FStar_Syntax_Syntax.mk uu____11683 in
                               uu____11680
                                 (Some
                                    (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                 r))
                           else
                             (let uu____11714 =
                                let uu____11717 =
                                  let uu____11718 =
                                    let uu____11728 =
                                      let uu____11729 =
                                        let uu____11730 =
                                          env.FStar_TypeChecker_Env.universe_of
                                            env
                                            c21.FStar_Syntax_Syntax.result_typ in
                                        [uu____11730] in
                                      FStar_TypeChecker_Env.inst_effect_fun_with
                                        uu____11729 env c2_decl
                                        c2_decl.FStar_Syntax_Syntax.stronger in
                                    let uu____11731 =
                                      let uu____11733 =
                                        FStar_Syntax_Syntax.as_arg
                                          c21.FStar_Syntax_Syntax.result_typ in
                                      let uu____11734 =
                                        let uu____11736 =
                                          FStar_Syntax_Syntax.as_arg wpc2 in
                                        let uu____11737 =
                                          let uu____11739 =
                                            let uu____11740 =
                                              (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                c11.FStar_Syntax_Syntax.result_typ
                                                wpc1 in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____11740 in
                                          [uu____11739] in
                                        uu____11736 :: uu____11737 in
                                      uu____11733 :: uu____11734 in
                                    (uu____11728, uu____11731) in
                                  FStar_Syntax_Syntax.Tm_app uu____11718 in
                                FStar_Syntax_Syntax.mk uu____11717 in
                              uu____11714
                                (Some
                                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                r) in
                       let base_prob =
                         let uu____11751 =
                           sub_prob c11.FStar_Syntax_Syntax.result_typ
                             problem.FStar_TypeChecker_Common.relation
                             c21.FStar_Syntax_Syntax.result_typ "result type" in
                         FStar_All.pipe_left
                           (fun _0_69  ->
                              FStar_TypeChecker_Common.TProb _0_69)
                           uu____11751 in
                       let wl1 =
                         let uu____11757 =
                           let uu____11759 =
                             let uu____11762 =
                               FStar_All.pipe_right (p_guard base_prob)
                                 Prims.fst in
                             FStar_Syntax_Util.mk_conj uu____11762 g in
                           FStar_All.pipe_left (fun _0_70  -> Some _0_70)
                             uu____11759 in
                         solve_prob orig uu____11757 [] wl in
                       solve env (attempt [base_prob] wl1)))) in
        let uu____11772 = FStar_Util.physical_equality c1 c2 in
        if uu____11772
        then
          let uu____11773 = solve_prob orig None [] wl in
          solve env uu____11773
        else
          ((let uu____11776 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____11776
            then
              let uu____11777 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____11778 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____11777
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____11778
            else ());
           (let uu____11780 =
              let uu____11783 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____11784 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____11783, uu____11784) in
            match uu____11780 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____11788),FStar_Syntax_Syntax.Total
                    (t2,uu____11790)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____11803 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11803 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____11806,FStar_Syntax_Syntax.Total uu____11807) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let uu____11856 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env uu____11856 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let uu____11863 =
                       let uu___174_11866 = problem in
                       let uu____11869 =
                         let uu____11870 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11870 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___174_11866.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11869;
                         FStar_TypeChecker_Common.relation =
                           (uu___174_11866.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___174_11866.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___174_11866.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___174_11866.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___174_11866.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___174_11866.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___174_11866.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___174_11866.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11863 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let uu____11875 =
                       let uu___175_11878 = problem in
                       let uu____11881 =
                         let uu____11882 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11882 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___175_11878.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___175_11878.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___175_11878.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11881;
                         FStar_TypeChecker_Common.element =
                           (uu___175_11878.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___175_11878.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___175_11878.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___175_11878.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___175_11878.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___175_11878.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____11875 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____11883,FStar_Syntax_Syntax.Comp uu____11884) ->
                     let uu____11885 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____11885
                     then
                       let uu____11886 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type" in
                       solve_t env uu____11886 wl
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
                           (let uu____11896 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____11896
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____11898 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____11898 with
                            | None  ->
                                let uu____11900 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____11901 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____11901) in
                                if uu____11900
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
                                  (let uu____11904 =
                                     let uu____11905 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____11906 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____11905 uu____11906 in
                                   giveup env uu____11904 orig)
                            | Some edge -> solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11911 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____11931  ->
              match uu____11931 with
              | (uu____11942,uu____11943,u,uu____11945,uu____11946,uu____11947)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____11911 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11976 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____11976 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____11986 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____11998  ->
                match uu____11998 with
                | (u1,u2) ->
                    let uu____12003 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____12004 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____12003 uu____12004)) in
      FStar_All.pipe_right uu____11986 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____12016,[])) -> "{}"
      | uu____12029 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____12039 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____12039
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____12042 =
              FStar_List.map
                (fun uu____12046  ->
                   match uu____12046 with
                   | (uu____12049,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____12042 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____12053 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____12053 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____12091 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____12091
    then
      let uu____12092 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____12093 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____12092
        (rel_to_string rel) uu____12093
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
            let uu____12113 =
              let uu____12115 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_71  -> Some _0_71) uu____12115 in
            FStar_Syntax_Syntax.new_bv uu____12113 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____12121 =
              let uu____12123 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_72  -> Some _0_72) uu____12123 in
            let uu____12125 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____12121 uu____12125 in
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
      fun err  ->
        let probs1 =
          let uu____12148 = FStar_Options.eager_inference () in
          if uu____12148
          then
            let uu___176_12149 = probs in
            {
              attempting = (uu___176_12149.attempting);
              wl_deferred = (uu___176_12149.wl_deferred);
              ctr = (uu___176_12149.ctr);
              defer_ok = false;
              smt_ok = (uu___176_12149.smt_ok);
              tcenv = (uu___176_12149.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____12160 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____12160
              then
                let uu____12161 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____12161
              else ());
             err (d, s))
let simplify_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____12171 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____12171
            then
              let uu____12172 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____12172
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____12176 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____12176
             then
               let uu____12177 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____12177
             else ());
            (let f2 =
               let uu____12180 =
                 let uu____12181 = FStar_Syntax_Util.unmeta f1 in
                 uu____12181.FStar_Syntax_Syntax.n in
               match uu____12180 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____12185 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___177_12186 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___177_12186.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___177_12186.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___177_12186.FStar_TypeChecker_Env.implicits)
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
            let uu____12201 =
              let uu____12202 =
                let uu____12203 =
                  let uu____12204 =
                    FStar_All.pipe_right (p_guard prob) Prims.fst in
                  FStar_All.pipe_right uu____12204
                    (fun _0_73  -> FStar_TypeChecker_Common.NonTrivial _0_73) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____12203;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____12202 in
            FStar_All.pipe_left (fun _0_74  -> Some _0_74) uu____12201
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
          (let uu____12231 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12231
           then
             let uu____12232 = FStar_Syntax_Print.term_to_string t1 in
             let uu____12233 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____12232
               uu____12233
           else ());
          (let prob =
             let uu____12236 =
               let uu____12239 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____12239 in
             FStar_All.pipe_left
               (fun _0_75  -> FStar_TypeChecker_Common.TProb _0_75)
               uu____12236 in
           let g =
             let uu____12244 =
               let uu____12246 = singleton' env prob smt_ok in
               solve_and_commit env uu____12246 (fun uu____12247  -> None) in
             FStar_All.pipe_left (with_guard env prob) uu____12244 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12261 = try_teq true env t1 t2 in
        match uu____12261 with
        | None  ->
            let uu____12263 =
              let uu____12264 =
                let uu____12267 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                let uu____12268 = FStar_TypeChecker_Env.get_range env in
                (uu____12267, uu____12268) in
              FStar_Errors.Error uu____12264 in
            Prims.raise uu____12263
        | Some g ->
            ((let uu____12271 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____12271
              then
                let uu____12272 = FStar_Syntax_Print.term_to_string t1 in
                let uu____12273 = FStar_Syntax_Print.term_to_string t2 in
                let uu____12274 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____12272
                  uu____12273 uu____12274
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
          (let uu____12290 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____12290
           then
             let uu____12291 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____12292 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____12291
               uu____12292
           else ());
          (let uu____12294 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____12294 with
           | (prob,x) ->
               let g =
                 let uu____12302 =
                   let uu____12304 = singleton' env prob smt_ok in
                   solve_and_commit env uu____12304
                     (fun uu____12305  -> None) in
                 FStar_All.pipe_left (with_guard env prob) uu____12302 in
               ((let uu____12311 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____12311
                 then
                   let uu____12312 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____12313 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____12314 =
                     let uu____12315 = FStar_Util.must g in
                     guard_to_string env uu____12315 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____12312 uu____12313 uu____12314
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
          let uu____12339 = FStar_TypeChecker_Env.get_range env in
          let uu____12340 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.report uu____12339 uu____12340
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____12352 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____12352
         then
           let uu____12353 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____12354 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____12353
             uu____12354
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____12359 =
             let uu____12362 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None uu____12362 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_76  -> FStar_TypeChecker_Common.CProb _0_76) uu____12359 in
         let uu____12365 =
           let uu____12367 = singleton env prob in
           solve_and_commit env uu____12367 (fun uu____12368  -> None) in
         FStar_All.pipe_left (with_guard env prob) uu____12365)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____12387  ->
        match uu____12387 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____12412 =
                 let uu____12413 =
                   let uu____12416 =
                     let uu____12417 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____12418 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____12417 uu____12418 in
                   let uu____12419 = FStar_TypeChecker_Env.get_range env in
                   (uu____12416, uu____12419) in
                 FStar_Errors.Error uu____12413 in
               Prims.raise uu____12412) in
            let equiv v1 v' =
              let uu____12427 =
                let uu____12430 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____12431 = FStar_Syntax_Subst.compress_univ v' in
                (uu____12430, uu____12431) in
              match uu____12427 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____12439 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____12453 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____12453 with
                      | FStar_Syntax_Syntax.U_unif uu____12457 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____12468  ->
                                    match uu____12468 with
                                    | (u,v') ->
                                        let uu____12474 = equiv v1 v' in
                                        if uu____12474
                                        then
                                          let uu____12476 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____12476 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____12486 -> [])) in
            let uu____12489 =
              let wl =
                let uu___178_12492 = empty_worklist env in
                {
                  attempting = (uu___178_12492.attempting);
                  wl_deferred = (uu___178_12492.wl_deferred);
                  ctr = (uu___178_12492.ctr);
                  defer_ok = false;
                  smt_ok = (uu___178_12492.smt_ok);
                  tcenv = (uu___178_12492.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____12499  ->
                      match uu____12499 with
                      | (lb,v1) ->
                          let uu____12504 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____12504 with
                           | USolved wl1 -> ()
                           | uu____12506 -> fail lb v1))) in
            let rec check_ineq uu____12512 =
              match uu____12512 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____12519) -> true
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
                   | (FStar_Syntax_Syntax.U_max us,uu____12535) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12539,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____12544 -> false) in
            let uu____12547 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____12553  ->
                      match uu____12553 with
                      | (u,v1) ->
                          let uu____12558 = check_ineq (u, v1) in
                          if uu____12558
                          then true
                          else
                            ((let uu____12561 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____12561
                              then
                                let uu____12562 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____12563 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____12562
                                  uu____12563
                              else ());
                             false))) in
            if uu____12547
            then ()
            else
              ((let uu____12567 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____12567
                then
                  ((let uu____12569 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____12569);
                   FStar_Unionfind.rollback tx;
                   (let uu____12575 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____12575))
                else ());
               (let uu____12581 =
                  let uu____12582 =
                    let uu____12585 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____12585) in
                  FStar_Errors.Error uu____12582 in
                Prims.raise uu____12581))
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
      let fail uu____12618 =
        match uu____12618 with
        | (d,s) ->
            let msg = explain env d s in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____12628 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____12628
       then
         let uu____12629 = wl_to_string wl in
         let uu____12630 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____12629 uu____12630
       else ());
      (let g1 =
         let uu____12642 = solve_and_commit env wl fail in
         match uu____12642 with
         | Some [] ->
             let uu___179_12649 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___179_12649.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_12649.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_12649.FStar_TypeChecker_Env.implicits)
             }
         | uu____12652 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___180_12655 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___180_12655.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___180_12655.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___180_12655.FStar_TypeChecker_Env.implicits)
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
            let uu___181_12681 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___181_12681.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___181_12681.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___181_12681.FStar_TypeChecker_Env.implicits)
            } in
          let uu____12682 =
            let uu____12683 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____12683 in
          if uu____12682
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____12689 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Norm") in
                   if uu____12689
                   then
                     let uu____12690 = FStar_TypeChecker_Env.get_range env in
                     let uu____12691 =
                       let uu____12692 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____12692 in
                     FStar_Errors.diag uu____12690 uu____12691
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
                         ((let uu____12701 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____12701
                           then
                             let uu____12702 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____12703 =
                               let uu____12704 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____12704 in
                             FStar_Errors.diag uu____12702 uu____12703
                           else ());
                          (let vcs =
                             let uu____12710 = FStar_Options.use_tactics () in
                             if uu____12710
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____12724  ->
                                   match uu____12724 with
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
      let uu____12735 = discharge_guard' None env g true in
      match uu____12735 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____12755 = FStar_Unionfind.find u in
      match uu____12755 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____12764 -> false in
    let rec until_fixpoint acc implicits =
      let uu____12779 = acc in
      match uu____12779 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____12825 = hd1 in
               (match uu____12825 with
                | (uu____12832,env,u,tm,k,r) ->
                    let uu____12838 = unresolved u in
                    if uu____12838
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____12856 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____12856
                        then
                          let uu____12857 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____12861 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____12862 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____12857 uu____12861 uu____12862
                        else ());
                       (let uu____12864 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___182_12868 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___182_12868.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___182_12868.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___182_12868.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___182_12868.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___182_12868.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___182_12868.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___182_12868.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___182_12868.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___182_12868.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___182_12868.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___182_12868.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___182_12868.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___182_12868.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___182_12868.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___182_12868.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___182_12868.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___182_12868.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___182_12868.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___182_12868.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___182_12868.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___182_12868.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___182_12868.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___182_12868.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____12864 with
                        | (uu____12869,uu____12870,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___183_12873 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___183_12873.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___183_12873.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___183_12873.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____12876 =
                                discharge_guard'
                                  (Some
                                     (fun uu____12880  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____12876 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___184_12895 = g in
    let uu____12896 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___184_12895.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___184_12895.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___184_12895.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12896
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____12924 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____12924 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____12931 = discharge_guard env g1 in
          FStar_All.pipe_left Prims.ignore uu____12931
      | (reason,uu____12933,uu____12934,e,t,r)::uu____12938 ->
          let uu____12952 =
            let uu____12953 = FStar_Syntax_Print.term_to_string t in
            let uu____12954 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____12953 uu____12954 reason in
          FStar_Errors.report r uu____12952
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___185_12961 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___185_12961.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___185_12961.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___185_12961.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12979 = try_teq false env t1 t2 in
        match uu____12979 with
        | None  -> false
        | Some g ->
            let uu____12982 = discharge_guard' None env g false in
            (match uu____12982 with
             | Some uu____12986 -> true
             | None  -> false)