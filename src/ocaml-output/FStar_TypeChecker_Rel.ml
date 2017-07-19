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
        FStar_TypeChecker_Env.univ_ineqs = uu____30;
        FStar_TypeChecker_Env.implicits = uu____31;_} -> true
    | uu____58 -> false
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
            FStar_TypeChecker_Env.deferred = uu____93;
            FStar_TypeChecker_Env.univ_ineqs = uu____94;
            FStar_TypeChecker_Env.implicits = uu____95;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____121 -> failwith "impossible" in
          let uu____122 =
            let uu___133_123 = g1 in
            let uu____124 =
              let uu____125 =
                let uu____126 =
                  let uu____127 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____127] in
                let uu____128 =
                  let uu____141 =
                    let uu____152 =
                      let uu____153 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
                      FStar_All.pipe_right uu____153
                        FStar_Syntax_Util.lcomp_of_comp in
                    FStar_All.pipe_right uu____152
                      (fun _0_29  -> FStar_Util.Inl _0_29) in
                  FStar_Pervasives_Native.Some uu____141 in
                FStar_Syntax_Util.abs uu____126 f uu____128 in
              FStar_All.pipe_left
                (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                uu____125 in
            {
              FStar_TypeChecker_Env.guard_f = uu____124;
              FStar_TypeChecker_Env.deferred =
                (uu___133_123.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_123.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_123.FStar_TypeChecker_Env.implicits)
            } in
          FStar_Pervasives_Native.Some uu____122
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___134_187 = g in
          let uu____188 =
            let uu____189 =
              let uu____190 =
                let uu____195 =
                  let uu____196 =
                    let uu____215 =
                      let uu____218 = FStar_Syntax_Syntax.as_arg e in
                      [uu____218] in
                    (f, uu____215) in
                  FStar_Syntax_Syntax.Tm_app uu____196 in
                FStar_Syntax_Syntax.mk uu____195 in
              uu____190
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
              uu____189 in
          {
            FStar_TypeChecker_Env.guard_f = uu____188;
            FStar_TypeChecker_Env.deferred =
              (uu___134_187.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___134_187.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___134_187.FStar_TypeChecker_Env.implicits)
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
          let uu___135_237 = g in
          let uu____238 =
            let uu____239 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____239 in
          {
            FStar_TypeChecker_Env.guard_f = uu____238;
            FStar_TypeChecker_Env.deferred =
              (uu___135_237.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_237.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_237.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____243 -> failwith "impossible"
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
          let uu____254 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____254
let check_trivial:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____267 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____298 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____298;
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
                       let uu____361 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____361
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___136_363 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___136_363.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_363.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_363.FStar_TypeChecker_Env.implicits)
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
               let uu____379 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____379
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
            let uu___137_392 = g in
            let uu____393 =
              let uu____394 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____394 in
            {
              FStar_TypeChecker_Env.guard_f = uu____393;
              FStar_TypeChecker_Env.deferred =
                (uu___137_392.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_392.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_392.FStar_TypeChecker_Env.implicits)
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
        | uu____456 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____483 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____483 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____505 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r in
            (uu____505, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____545 = FStar_Syntax_Util.type_u () in
        match uu____545 with
        | (t_type,u) ->
            let uu____552 =
              let uu____557 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____557 t_type in
            (match uu____552 with
             | (tt,uu____559) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____592 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____632 -> false
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
    match projectee with | Success _0 -> true | uu____740 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____756 -> false
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
    match projectee with | COVARIANT  -> true | uu____779 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____783 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____787 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_810  ->
    match uu___105_810 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____823 =
    let uu____824 = FStar_Syntax_Subst.compress t in
    uu____824.FStar_Syntax_Syntax.n in
  match uu____823 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____855 = FStar_Syntax_Print.uvar_to_string u in
      let uu____862 = FStar_Syntax_Print.term_to_string t1 in
      FStar_Util.format2 "(%s:%s)" uu____855 uu____862
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____865;
         FStar_Syntax_Syntax.pos = uu____866;
         FStar_Syntax_Syntax.vars = uu____867;_},args)
      ->
      let uu____921 = FStar_Syntax_Print.uvar_to_string u in
      let uu____928 = FStar_Syntax_Print.term_to_string ty in
      let uu____929 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" uu____921 uu____928 uu____929
  | uu____930 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_936  ->
      match uu___106_936 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____942 =
            let uu____945 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____946 =
              let uu____949 =
                term_to_string env p.FStar_TypeChecker_Common.lhs in
              let uu____950 =
                let uu____953 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let uu____954 =
                  let uu____957 =
                    let uu____960 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let uu____961 =
                      let uu____964 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let uu____965 =
                        let uu____968 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let uu____969 =
                          let uu____972 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [uu____972] in
                        uu____968 :: uu____969 in
                      uu____964 :: uu____965 in
                    uu____960 :: uu____961 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____957 in
                uu____953 :: uu____954 in
              uu____949 :: uu____950 in
            uu____945 :: uu____946 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____942
      | FStar_TypeChecker_Common.CProb p ->
          let uu____980 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____981 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____980
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____981
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_987  ->
      match uu___107_987 with
      | UNIV (u,t) ->
          let x =
            let uu____991 = FStar_Options.hide_uvar_nums () in
            if uu____991
            then "?"
            else
              (let uu____993 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____993 FStar_Util.string_of_int) in
          let uu____996 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____996
      | TERM ((u,uu____998),t) ->
          let x =
            let uu____1005 = FStar_Options.hide_uvar_nums () in
            if uu____1005
            then "?"
            else
              (let uu____1007 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____1007 FStar_Util.string_of_int) in
          let uu____1014 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____1014
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____1025 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____1025 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____1037 =
      let uu____1040 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1040
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1037 (FStar_String.concat ", ")
let args_to_string args =
  let uu____1068 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____1083  ->
            match uu____1083 with
            | (x,uu____1089) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right uu____1068 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1095 =
      let uu____1096 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1096 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1095;
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
        let uu___138_1112 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___138_1112.wl_deferred);
          ctr = (uu___138_1112.ctr);
          defer_ok = (uu___138_1112.defer_ok);
          smt_ok;
          tcenv = (uu___138_1112.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___139_1143 = empty_worklist env in
  let uu____1144 = FStar_List.map FStar_Pervasives_Native.snd g in
  {
    attempting = uu____1144;
    wl_deferred = (uu___139_1143.wl_deferred);
    ctr = (uu___139_1143.ctr);
    defer_ok = false;
    smt_ok = (uu___139_1143.smt_ok);
    tcenv = (uu___139_1143.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_1158 = wl in
        {
          attempting = (uu___140_1158.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_1158.ctr);
          defer_ok = (uu___140_1158.defer_ok);
          smt_ok = (uu___140_1158.smt_ok);
          tcenv = (uu___140_1158.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___141_1175 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_1175.wl_deferred);
        ctr = (uu___141_1175.ctr);
        defer_ok = (uu___141_1175.defer_ok);
        smt_ok = (uu___141_1175.smt_ok);
        tcenv = (uu___141_1175.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1186 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1186
         then
           let uu____1187 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1187
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_1191  ->
    match uu___108_1191 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___142_1213 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_1213.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_1213.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_1213.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_1213.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_1213.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_1213.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_1213.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_1242  ->
    match uu___109_1242 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_1266  ->
      match uu___110_1266 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_1269  ->
    match uu___111_1269 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_1282  ->
    match uu___112_1282 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_1297  ->
    match uu___113_1297 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_1312  ->
    match uu___114_1312 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___115_1329  ->
    match uu___115_1329 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_1346  ->
    match uu___116_1346 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_1359  ->
    match uu___117_1359 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1381 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1381 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1391  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1445 = next_pid () in
  let uu____1446 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1445;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1446;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let uu____1499 = next_pid () in
  let uu____1500 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = uu____1499;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1500;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1547 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = uu____1547;
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
        let uu____1617 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1617
        then
          let uu____1618 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1619 = prob_to_string env d in
          let uu____1620 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1618 uu____1619 uu____1620 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1626 -> failwith "impossible" in
           let uu____1627 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1641 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1642 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1641, uu____1642)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1648 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1649 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1648, uu____1649) in
           match uu____1627 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1661  ->
            match uu___118_1661 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1671 ->
                     FStar_Unionfind.change u
                       (FStar_Pervasives_Native.Some t))
            | TERM ((u,uu____1675),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1713  ->
           match uu___119_1713 with
           | UNIV uu____1716 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1722),t) ->
               let uu____1728 = FStar_Unionfind.equivalent uv u in
               if uu____1728
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
        (fun uu___120_1758  ->
           match uu___120_1758 with
           | UNIV (u',t) ->
               let uu____1763 = FStar_Unionfind.equivalent u u' in
               if uu____1763
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1769 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1776 =
        let uu____1777 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1777 in
      FStar_Syntax_Subst.compress uu____1776
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1784 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1784
let norm_arg env t =
  let uu____1809 = sn env (FStar_Pervasives_Native.fst t) in
  (uu____1809, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1836  ->
              match uu____1836 with
              | (x,imp) ->
                  let uu____1847 =
                    let uu___143_1848 = x in
                    let uu____1849 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1848.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1848.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1849
                    } in
                  (uu____1847, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1866 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1866
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1870 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1870
        | uu____1873 -> u2 in
      let uu____1874 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1874
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
          (let uu____2038 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           match uu____2038 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____2059;
               FStar_Syntax_Syntax.pos = uu____2060;
               FStar_Syntax_Syntax.vars = uu____2061;_} ->
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____2101 =
                 let uu____2102 = FStar_Syntax_Print.term_to_string tt in
                 let uu____2103 = FStar_Syntax_Print.tag_of_term tt in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____2102
                   uu____2103 in
               failwith uu____2101)
    | FStar_Syntax_Syntax.Tm_uinst uu____2122 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____2173 =
             let uu____2174 = FStar_Syntax_Subst.compress t1' in
             uu____2174.FStar_Syntax_Syntax.n in
           match uu____2173 with
           | FStar_Syntax_Syntax.Tm_refine uu____2197 -> aux true t1'
           | uu____2206 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____2229 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____2272 =
             let uu____2273 = FStar_Syntax_Subst.compress t1' in
             uu____2273.FStar_Syntax_Syntax.n in
           match uu____2272 with
           | FStar_Syntax_Syntax.Tm_refine uu____2296 -> aux true t1'
           | uu____2305 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____2328 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11 in
           let uu____2389 =
             let uu____2390 = FStar_Syntax_Subst.compress t1' in
             uu____2390.FStar_Syntax_Syntax.n in
           match uu____2389 with
           | FStar_Syntax_Syntax.Tm_refine uu____2413 -> aux true t1'
           | uu____2422 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____2445 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____2468 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____2491 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____2514 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____2537 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____2574 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____2625 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____2664 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____2701 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____2754 ->
        let uu____2763 =
          let uu____2764 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2765 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2764
            uu____2765 in
        failwith uu____2763
    | FStar_Syntax_Syntax.Tm_ascribed uu____2784 ->
        let uu____2819 =
          let uu____2820 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2821 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2820
            uu____2821 in
        failwith uu____2819
    | FStar_Syntax_Syntax.Tm_delayed uu____2840 ->
        let uu____2879 =
          let uu____2880 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2881 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2880
            uu____2881 in
        failwith uu____2879
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____2900 =
          let uu____2901 = FStar_Syntax_Print.term_to_string t11 in
          let uu____2902 = FStar_Syntax_Print.tag_of_term t11 in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2901
            uu____2902 in
        failwith uu____2900 in
  let uu____2921 = whnf env t1 in aux false uu____2921
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____2932 =
        let uu____2951 = empty_worklist env in
        base_and_refinement env uu____2951 t in
      FStar_All.pipe_right uu____2932 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2995 = FStar_Syntax_Syntax.null_bv t in
    (uu____2995, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____3017 = base_and_refinement env wl t in
  match uu____3017 with
  | (t_base,refinement) ->
      (match refinement with
       | FStar_Pervasives_Native.None  -> trivial_refinement t_base
       | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement uu____3124 =
  match uu____3124 with
  | (t_base,refopt) ->
      let uu____3149 =
        match refopt with
        | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
        | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
      (match uu____3149 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_3179  ->
      match uu___121_3179 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____3185 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____3186 =
            let uu____3187 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
            FStar_Syntax_Print.term_to_string uu____3187 in
          let uu____3188 =
            let uu____3189 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
            FStar_Syntax_Print.term_to_string uu____3189 in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____3185 uu____3186
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____3188
      | FStar_TypeChecker_Common.CProb p ->
          let uu____3195 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____3196 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let uu____3197 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____3195 uu____3196
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____3197
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____3201 =
      let uu____3204 =
        let uu____3207 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3226  ->
                  match uu____3226 with | (uu____3233,uu____3234,x) -> x)) in
        FStar_List.append wl.attempting uu____3207 in
      FStar_List.map (wl_prob_to_string wl) uu____3204 in
    FStar_All.pipe_right uu____3201 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3259 =
          let uu____3278 =
            let uu____3279 = FStar_Syntax_Subst.compress k in
            uu____3279.FStar_Syntax_Syntax.n in
          match uu____3278 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3350 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3350)
              else
                (let uu____3376 = FStar_Syntax_Util.abs_formals t in
                 match uu____3376 with
                 | (ys',t1,uu____3415) ->
                     let uu____3440 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3440))
          | uu____3481 ->
              let uu____3482 =
                let uu____3493 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3493) in
              ((ys, t), uu____3482) in
        match uu____3259 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr (FStar_Parser_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____3588 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3588 c in
               let uu____3591 =
                 let uu____3604 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36) in
                 FStar_All.pipe_right uu____3604
                   (fun _0_37  -> FStar_Pervasives_Native.Some _0_37) in
               FStar_Syntax_Util.abs ys1 t1 uu____3591)
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
            let uu____3688 = p_guard prob in
            match uu____3688 with
            | (uu____3693,uv) ->
                ((let uu____3696 =
                    let uu____3697 = FStar_Syntax_Subst.compress uv in
                    uu____3697.FStar_Syntax_Syntax.n in
                  match uu____3696 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3731 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3731
                        then
                          let uu____3732 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3733 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3734 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3732
                            uu____3733 uu____3734
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3740 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_3743 = wl in
                  {
                    attempting = (uu___144_3743.attempting);
                    wl_deferred = (uu___144_3743.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_3743.defer_ok);
                    smt_ok = (uu___144_3743.smt_ok);
                    tcenv = (uu___144_3743.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3758 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3758
         then
           let uu____3759 = FStar_Util.string_of_int pid in
           let uu____3760 =
             let uu____3761 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3761 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3759 uu____3760
         else ());
        commit sol;
        (let uu___145_3768 = wl in
         {
           attempting = (uu___145_3768.attempting);
           wl_deferred = (uu___145_3768.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_3768.defer_ok);
           smt_ok = (uu___145_3768.smt_ok);
           tcenv = (uu___145_3768.tcenv)
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
            | (uu____3806,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3818 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3818 in
          (let uu____3828 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3828
           then
             let uu____3829 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3830 =
               let uu____3831 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3831 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3829 uu____3830
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let uu____3862 =
    let uu____3869 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right uu____3869 FStar_Util.set_elements in
  FStar_All.pipe_right uu____3862
    (FStar_Util.for_some
       (fun uu____3910  ->
          match uu____3910 with
          | (uv,uu____3924) ->
              FStar_Unionfind.equivalent uv (FStar_Pervasives_Native.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____3986 = occurs wl uk t in Prims.op_Negation uu____3986 in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____3993 =
         let uu____3994 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk) in
         let uu____4001 = FStar_Syntax_Print.term_to_string t in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____3994 uu____4001 in
       FStar_Pervasives_Native.Some uu____3993) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____4066 = occurs_check env wl uk t in
  match uu____4066 with
  | (occurs_ok,msg) ->
      let uu____4097 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, uu____4097, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set1 v1 in
  let uu____4203 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____4250  ->
            fun uu____4251  ->
              match (uu____4250, uu____4251) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____4332 =
                    let uu____4333 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation uu____4333 in
                  if uu____4332
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____4358 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____4358
                     then
                       let uu____4371 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), uu____4371)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____4203 with | (isect,uu____4412) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____4487  ->
          fun uu____4488  ->
            match (uu____4487, uu____4488) with
            | ((a,uu____4506),(b,uu____4508)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____4574 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____4585  ->
                match uu____4585 with
                | (b,uu____4591) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____4574
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____4607 -> FStar_Pervasives_Native.None
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
            let uu____4681 = pat_var_opt env seen hd1 in
            (match uu____4681 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4695 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4695
                   then
                     let uu____4696 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4696
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4714 =
      let uu____4715 = FStar_Syntax_Subst.compress t in
      uu____4715.FStar_Syntax_Syntax.n in
    match uu____4714 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4720 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4737;
           FStar_Syntax_Syntax.tk = uu____4738;
           FStar_Syntax_Syntax.pos = uu____4739;
           FStar_Syntax_Syntax.vars = uu____4740;_},uu____4741)
        -> true
    | uu____4786 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____4898;
         FStar_Syntax_Syntax.pos = uu____4899;
         FStar_Syntax_Syntax.vars = uu____4900;_},args)
      -> (t, uv, k, args)
  | uu____4980 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____5075 = destruct_flex_t t in
  match uu____5075 with
  | (t1,uv,k,args) ->
      let uu____5206 = pat_vars env [] args in
      (match uu____5206 with
       | FStar_Pervasives_Native.Some vars ->
           ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
       | uu____5316 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5405 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5440 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5444 -> false
let head_match: match_result -> match_result =
  fun uu___122_5447  ->
    match uu___122_5447 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5462 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5475 ->
          let uu____5476 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5476 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5491 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5510 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5521 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5562 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5563 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5564 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5581 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5596 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5628) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5638,uu____5639) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5697) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5726;
             FStar_Syntax_Syntax.index = uu____5727;
             FStar_Syntax_Syntax.sort = t2;_},uu____5729)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5742 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5743 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5744 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5759 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5789 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5789
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
            let uu____5810 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5810
            then FullMatch
            else
              (let uu____5812 =
                 let uu____5821 =
                   let uu____5824 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5824 in
                 let uu____5825 =
                   let uu____5828 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5828 in
                 (uu____5821, uu____5825) in
               MisMatch uu____5812)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5834),FStar_Syntax_Syntax.Tm_uinst (g,uu____5836)) ->
            let uu____5853 = head_matches env f g in
            FStar_All.pipe_right uu____5853 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5862),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5864)) ->
            let uu____5913 = FStar_Unionfind.equivalent uv uv' in
            if uu____5913
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5926),FStar_Syntax_Syntax.Tm_refine (y,uu____5928)) ->
            let uu____5945 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5945 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5947),uu____5948) ->
            let uu____5957 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5957 head_match
        | (uu____5958,FStar_Syntax_Syntax.Tm_refine (x,uu____5960)) ->
            let uu____5969 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5969 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5970,FStar_Syntax_Syntax.Tm_type
           uu____5971) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5972,FStar_Syntax_Syntax.Tm_arrow uu____5973) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6003),FStar_Syntax_Syntax.Tm_app (head',uu____6005))
            ->
            let uu____6062 = head_matches env head1 head' in
            FStar_All.pipe_right uu____6062 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6064),uu____6065) ->
            let uu____6094 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____6094 head_match
        | (uu____6095,FStar_Syntax_Syntax.Tm_app (head1,uu____6097)) ->
            let uu____6126 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____6126 head_match
        | uu____6127 ->
            let uu____6132 =
              let uu____6141 = delta_depth_of_term env t11 in
              let uu____6144 = delta_depth_of_term env t21 in
              (uu____6141, uu____6144) in
            MisMatch uu____6132
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____6189 = FStar_Syntax_Util.head_and_args t in
    match uu____6189 with
    | (head1,uu____6211) ->
        let uu____6240 =
          let uu____6241 = FStar_Syntax_Util.un_uinst head1 in
          uu____6241.FStar_Syntax_Syntax.n in
        (match uu____6240 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____6249 =
               let uu____6250 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right uu____6250 FStar_Option.isSome in
             if uu____6249
             then
               let uu____6273 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right uu____6273
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
             else FStar_Pervasives_Native.None
         | uu____6277 -> FStar_Pervasives_Native.None) in
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
         ),uu____6380)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____6398 =
             let uu____6407 = maybe_inline t11 in
             let uu____6410 = maybe_inline t21 in (uu____6407, uu____6410) in
           match uu____6398 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____6447,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____6465 =
             let uu____6474 = maybe_inline t11 in
             let uu____6477 = maybe_inline t21 in (uu____6474, uu____6477) in
           match uu____6465 with
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
        let uu____6520 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____6520 with
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
        let uu____6543 =
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
             let uu____6555 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21 in
             (t11, uu____6555)) in
        (match uu____6543 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____6568 -> fail r
    | uu____6577 -> success n_delta r t11 t21 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6610 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6646 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6662 = FStar_Syntax_Util.type_u () in
      match uu____6662 with
      | (t,uu____6668) ->
          let uu____6669 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6669
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6680 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6680 FStar_Pervasives_Native.fst
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
        let uu____6744 = head_matches env t1 t' in
        match uu____6744 with
        | MisMatch uu____6745 -> false
        | uu____6754 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6860,imp),T (t2,uu____6863)) -> (t2, imp)
                     | uu____6888 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6958  ->
                    match uu____6958 with
                    | (t2,uu____6972) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____7021 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____7021 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____7102))::tcs2) ->
                       aux
                         (((let uu___146_7136 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_7136.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_7136.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____7154 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___123_7209 =
                 match uu___123_7209 with
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
               let uu____7328 = decompose1 [] bs1 in
               (rebuild, matches, uu____7328))
      | uu____7379 ->
          let rebuild uu___124_7385 =
            match uu___124_7385 with
            | [] -> t1
            | uu____7388 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___125_7418  ->
    match uu___125_7418 with
    | T (t,uu____7420) -> t
    | uu____7429 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_7432  ->
    match uu___126_7432 with
    | T (t,uu____7434) -> FStar_Syntax_Syntax.as_arg t
    | uu____7443 -> failwith "Impossible"
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
              | (uu____7553,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7578 = new_uvar r scope1 k in
                  (match uu____7578 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7598 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7619 =
                         let uu____7620 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____7620 in
                       ((T (gi_xs, mk_kind)), uu____7619))
              | (uu____7633,uu____7634,C uu____7635) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7796 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____7813;
                         FStar_Syntax_Syntax.pos = uu____7814;
                         FStar_Syntax_Syntax.vars = uu____7815;_})
                        ->
                        let uu____7844 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7844 with
                         | (T (gi_xs,uu____7870),prob) ->
                             let uu____7880 =
                               let uu____7881 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____7881 in
                             (uu____7880, [prob])
                         | uu____7884 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____7899;
                         FStar_Syntax_Syntax.pos = uu____7900;
                         FStar_Syntax_Syntax.vars = uu____7901;_})
                        ->
                        let uu____7930 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7930 with
                         | (T (gi_xs,uu____7956),prob) ->
                             let uu____7966 =
                               let uu____7967 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____7967 in
                             (uu____7966, [prob])
                         | uu____7970 -> failwith "impossible")
                    | (uu____7981,uu____7982,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____7984;
                         FStar_Syntax_Syntax.pos = uu____7985;
                         FStar_Syntax_Syntax.vars = uu____7986;_})
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
                        let uu____8122 =
                          let uu____8131 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____8131 FStar_List.unzip in
                        (match uu____8122 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____8185 =
                                 let uu____8186 =
                                   let uu____8191 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____8191 un_T in
                                 let uu____8192 =
                                   let uu____8203 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____8203
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____8186;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____8192;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____8185 in
                             ((C gi_xs), sub_probs))
                    | uu____8212 ->
                        let uu____8225 = sub_prob scope1 args q in
                        (match uu____8225 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7796 with
                   | (tc,probs) ->
                       let uu____8256 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____8306,uu____8307) ->
                             let uu____8322 =
                               let uu____8329 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b in
                               uu____8329 :: args in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____8322)
                         | uu____8364 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____8256 with
                        | (bopt,scope2,args1) ->
                            let uu____8446 = aux scope2 args1 qs2 in
                            (match uu____8446 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____8483 =
                                         let uu____8486 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____8486 in
                                       FStar_Syntax_Util.mk_conj_l uu____8483
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____8508 =
                                         let uu____8511 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____8512 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____8511 :: uu____8512 in
                                       FStar_Syntax_Util.mk_conj_l uu____8508 in
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
  let uu___147_8600 = p in
  let uu____8605 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let uu____8606 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_8600.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____8605;
    FStar_TypeChecker_Common.relation =
      (uu___147_8600.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____8606;
    FStar_TypeChecker_Common.element =
      (uu___147_8600.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_8600.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_8600.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_8600.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_8600.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_8600.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8618 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8618
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____8627 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8647 = compress_prob wl pr in
        FStar_All.pipe_right uu____8647 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8657 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8657 with
           | (lh,uu____8681) ->
               let uu____8710 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8710 with
                | (rh,uu____8734) ->
                    let uu____8763 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8780,FStar_Syntax_Syntax.Tm_uvar uu____8781)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8818,uu____8819)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8840,FStar_Syntax_Syntax.Tm_uvar uu____8841)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8862,uu____8863)
                          ->
                          let uu____8880 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8880 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8957 ->
                                    let rank =
                                      let uu____8969 = is_top_level_prob prob in
                                      if uu____8969
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8971 =
                                      let uu___148_8976 = tp in
                                      let uu____8981 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_8976.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_8976.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_8976.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8981;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_8976.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_8976.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_8976.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_8976.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_8976.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_8976.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8971)))
                      | (uu____9000,FStar_Syntax_Syntax.Tm_uvar uu____9001)
                          ->
                          let uu____9018 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____9018 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____9095 ->
                                    let uu____9106 =
                                      let uu___149_9115 = tp in
                                      let uu____9120 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_9115.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____9120;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_9115.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_9115.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_9115.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_9115.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_9115.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_9115.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_9115.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_9115.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____9106)))
                      | (uu____9151,uu____9152) -> (rigid_rigid, tp) in
                    (match uu____8763 with
                     | (rank,tp1) ->
                         let uu____9171 =
                           FStar_All.pipe_right
                             (let uu___150_9176 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_9176.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_9176.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_9176.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_9176.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_9176.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_9176.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_9176.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_9176.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_9176.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43) in
                         (rank, uu____9171))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9186 =
            FStar_All.pipe_right
              (let uu___151_9191 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_9191.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_9191.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_9191.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_9191.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_9191.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_9191.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_9191.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_9191.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_9191.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) in
          (rigid_rigid, uu____9186)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____9246 probs =
      match uu____9246 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____9299 = rank wl hd1 in
               (match uu____9299 with
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
    match projectee with | UDeferred _0 -> true | uu____9406 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9418 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9430 -> false
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
                        let uu____9473 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9473 with
                        | (k,uu____9479) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____9487 -> false)))
            | uu____9488 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____9539 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____9539 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____9542 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____9552 =
                     let uu____9553 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____9554 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____9553
                       uu____9554 in
                   UFailed uu____9552)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9574 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9574 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9596 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9596 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____9599 ->
                let uu____9604 =
                  let uu____9605 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____9606 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9605
                    uu____9606 msg in
                UFailed uu____9604 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9607,uu____9608) ->
              let uu____9609 =
                let uu____9610 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9611 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9610 uu____9611 in
              failwith uu____9609
          | (FStar_Syntax_Syntax.U_unknown ,uu____9612) ->
              let uu____9613 =
                let uu____9614 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9615 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9614 uu____9615 in
              failwith uu____9613
          | (uu____9616,FStar_Syntax_Syntax.U_bvar uu____9617) ->
              let uu____9618 =
                let uu____9619 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9620 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9619 uu____9620 in
              failwith uu____9618
          | (uu____9621,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9622 =
                let uu____9623 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9624 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9623 uu____9624 in
              failwith uu____9622
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9640 = FStar_Unionfind.equivalent v1 v2 in
              if uu____9640
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9656 = occurs_univ v1 u3 in
              if uu____9656
              then
                let uu____9657 =
                  let uu____9658 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9659 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9658 uu____9659 in
                try_umax_components u11 u21 uu____9657
              else
                (let uu____9661 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9661)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9673 = occurs_univ v1 u3 in
              if uu____9673
              then
                let uu____9674 =
                  let uu____9675 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9676 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9675 uu____9676 in
                try_umax_components u11 u21 uu____9674
              else
                (let uu____9678 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9678)
          | (FStar_Syntax_Syntax.U_max uu____9683,uu____9684) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9690 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9690
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9692,FStar_Syntax_Syntax.U_max uu____9693) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9699 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9699
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9701,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9702,FStar_Syntax_Syntax.U_name
             uu____9703) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9704) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9705) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9706,FStar_Syntax_Syntax.U_succ
             uu____9707) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9708,FStar_Syntax_Syntax.U_zero
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
  let uu____9794 = bc1 in
  match uu____9794 with
  | (bs1,mk_cod1) ->
      let uu____9835 = bc2 in
      (match uu____9835 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____9905 = FStar_Util.first_N n1 bs in
             match uu____9905 with
             | (bs3,rest) ->
                 let uu____9930 = mk_cod rest in (bs3, uu____9930) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let uu____9955 =
               let uu____9962 = mk_cod1 [] in (bs1, uu____9962) in
             let uu____9965 =
               let uu____9972 = mk_cod2 [] in (bs2, uu____9972) in
             (uu____9955, uu____9965)
           else
             if l1 > l2
             then
               (let uu____10009 = curry l2 bs1 mk_cod1 in
                let uu____10019 =
                  let uu____10026 = mk_cod2 [] in (bs2, uu____10026) in
                (uu____10009, uu____10019))
             else
               (let uu____10042 =
                  let uu____10049 = mk_cod1 [] in (bs1, uu____10049) in
                let uu____10052 = curry l1 bs2 mk_cod2 in
                (uu____10042, uu____10052)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____10170 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10170
       then
         let uu____10171 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10171
       else ());
      (let uu____10173 = next_prob probs in
       match uu____10173 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_10194 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___152_10194.wl_deferred);
               ctr = (uu___152_10194.ctr);
               defer_ok = (uu___152_10194.defer_ok);
               smt_ok = (uu___152_10194.smt_ok);
               tcenv = (uu___152_10194.tcenv)
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
                  let uu____10205 = solve_flex_rigid_join env tp probs1 in
                  (match uu____10205 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____10210 = solve_rigid_flex_meet env tp probs1 in
                     match uu____10210 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____10215,uu____10216) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____10233 ->
                let uu____10242 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10297  ->
                          match uu____10297 with
                          | (c,uu____10305,uu____10306) -> c < probs.ctr)) in
                (match uu____10242 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10347 =
                            FStar_List.map
                              (fun uu____10358  ->
                                 match uu____10358 with
                                 | (uu____10369,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____10347
                      | uu____10372 ->
                          let uu____10381 =
                            let uu___153_10382 = probs in
                            let uu____10383 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10400  ->
                                      match uu____10400 with
                                      | (uu____10407,uu____10408,y) -> y)) in
                            {
                              attempting = uu____10383;
                              wl_deferred = rest;
                              ctr = (uu___153_10382.ctr);
                              defer_ok = (uu___153_10382.defer_ok);
                              smt_ok = (uu___153_10382.smt_ok);
                              tcenv = (uu___153_10382.tcenv)
                            } in
                          solve env uu____10381))))
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
            let uu____10415 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____10415 with
            | USolved wl1 ->
                let uu____10417 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____10417
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
                  let uu____10463 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____10463 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10466 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____10478;
                  FStar_Syntax_Syntax.pos = uu____10479;
                  FStar_Syntax_Syntax.vars = uu____10480;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____10483;
                  FStar_Syntax_Syntax.pos = uu____10484;
                  FStar_Syntax_Syntax.vars = uu____10485;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10507,uu____10508) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10517,FStar_Syntax_Syntax.Tm_uinst uu____10518) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10527 -> USolved wl
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
            ((let uu____10537 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____10537
              then
                let uu____10538 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10538 msg
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
        (let uu____10547 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10547
         then
           let uu____10548 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10548
         else ());
        (let uu____10550 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____10550 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10624 = head_matches_delta env () t1 t2 in
               match uu____10624 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10665 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10714 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10729 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10730 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10729, uu____10730)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10735 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10736 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10735, uu____10736) in
                        (match uu____10714 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10770 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____10770 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10811 =
                                    let uu____10822 =
                                      let uu____10827 =
                                        let uu____10832 =
                                          let uu____10833 =
                                            let uu____10842 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10842) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10833 in
                                        FStar_Syntax_Syntax.mk uu____10832 in
                                      uu____10827
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10855 =
                                      let uu____10858 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10858] in
                                    (uu____10822, uu____10855) in
                                  FStar_Pervasives_Native.Some uu____10811
                              | (uu____10875,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10877)) ->
                                  let uu____10886 =
                                    let uu____10893 =
                                      let uu____10896 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10896] in
                                    (t11, uu____10893) in
                                  FStar_Pervasives_Native.Some uu____10886
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10906),uu____10907) ->
                                  let uu____10916 =
                                    let uu____10923 =
                                      let uu____10926 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10926] in
                                    (t21, uu____10923) in
                                  FStar_Pervasives_Native.Some uu____10916
                              | uu____10935 ->
                                  let uu____10940 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10940 with
                                   | (head1,uu____10968) ->
                                       let uu____10997 =
                                         let uu____10998 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10998.FStar_Syntax_Syntax.n in
                                       (match uu____10997 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____11011;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____11013;_}
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
                                        | uu____11026 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11041) ->
                  let uu____11066 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_11083  ->
                            match uu___127_11083 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____11090 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____11090 with
                                      | (u',uu____11110) ->
                                          let uu____11139 =
                                            let uu____11140 = whnf env u' in
                                            uu____11140.FStar_Syntax_Syntax.n in
                                          (match uu____11139 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____11146) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____11177 -> false))
                                 | uu____11178 -> false)
                            | uu____11181 -> false)) in
                  (match uu____11066 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____11215 tps =
                         match uu____11215 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____11263 =
                                    let uu____11272 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____11272 in
                                  (match uu____11263 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____11307 -> FStar_Pervasives_Native.None) in
                       let uu____11316 =
                         let uu____11325 =
                           let uu____11332 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____11332, []) in
                         make_lower_bound uu____11325 lower_bounds in
                       (match uu____11316 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____11344 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____11344
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
                            ((let uu____11364 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____11364
                              then
                                let wl' =
                                  let uu___154_11366 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___154_11366.wl_deferred);
                                    ctr = (uu___154_11366.ctr);
                                    defer_ok = (uu___154_11366.defer_ok);
                                    smt_ok = (uu___154_11366.smt_ok);
                                    tcenv = (uu___154_11366.tcenv)
                                  } in
                                let uu____11367 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____11367
                              else ());
                             (let uu____11369 =
                                solve_t env eq_prob
                                  (let uu___155_11370 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_11370.wl_deferred);
                                     ctr = (uu___155_11370.ctr);
                                     defer_ok = (uu___155_11370.defer_ok);
                                     smt_ok = (uu___155_11370.smt_ok);
                                     tcenv = (uu___155_11370.tcenv)
                                   }) in
                              match uu____11369 with
                              | Success uu____11373 ->
                                  let wl1 =
                                    let uu___156_11375 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_11375.wl_deferred);
                                      ctr = (uu___156_11375.ctr);
                                      defer_ok = (uu___156_11375.defer_ok);
                                      smt_ok = (uu___156_11375.smt_ok);
                                      tcenv = (uu___156_11375.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____11377 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____11380 -> FStar_Pervasives_Native.None))))
              | uu____11381 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____11390 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____11390
         then
           let uu____11391 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____11391
         else ());
        (let uu____11393 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____11393 with
         | (u,args) ->
             let uu____11444 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____11444 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____11485 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____11485 with
                    | (h1,args1) ->
                        let uu____11538 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____11538 with
                         | (h2,uu____11562) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11597 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____11597
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11617 =
                                          let uu____11620 =
                                            let uu____11621 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____11621 in
                                          [uu____11620] in
                                        FStar_Pervasives_Native.Some
                                          uu____11617))
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
                                       (let uu____11656 =
                                          let uu____11659 =
                                            let uu____11660 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____11660 in
                                          [uu____11659] in
                                        FStar_Pervasives_Native.Some
                                          uu____11656))
                                  else FStar_Pervasives_Native.None
                              | uu____11674 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11788 =
                               let uu____11799 =
                                 let uu____11804 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11804 in
                               (uu____11799, m1) in
                             FStar_Pervasives_Native.Some uu____11788)
                    | (uu____11821,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11823)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11883),uu____11884) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11943 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12006) ->
                       let uu____12031 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_12048  ->
                                 match uu___128_12048 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____12055 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____12055 with
                                           | (u',uu____12075) ->
                                               let uu____12104 =
                                                 let uu____12105 =
                                                   whnf env u' in
                                                 uu____12105.FStar_Syntax_Syntax.n in
                                               (match uu____12104 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____12111) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____12142 -> false))
                                      | uu____12143 -> false)
                                 | uu____12146 -> false)) in
                       (match uu____12031 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____12188 tps =
                              match uu____12188 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____12264 =
                                         let uu____12277 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____12277 in
                                       (match uu____12264 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____12344 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____12357 =
                              let uu____12370 =
                                let uu____12381 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____12381, []) in
                              make_upper_bound uu____12370 upper_bounds in
                            (match uu____12357 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____12397 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____12397
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
                                 ((let uu____12429 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____12429
                                   then
                                     let wl' =
                                       let uu___157_12431 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_12431.wl_deferred);
                                         ctr = (uu___157_12431.ctr);
                                         defer_ok = (uu___157_12431.defer_ok);
                                         smt_ok = (uu___157_12431.smt_ok);
                                         tcenv = (uu___157_12431.tcenv)
                                       } in
                                     let uu____12432 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____12432
                                   else ());
                                  (let uu____12434 =
                                     solve_t env eq_prob
                                       (let uu___158_12435 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_12435.wl_deferred);
                                          ctr = (uu___158_12435.ctr);
                                          defer_ok =
                                            (uu___158_12435.defer_ok);
                                          smt_ok = (uu___158_12435.smt_ok);
                                          tcenv = (uu___158_12435.tcenv)
                                        }) in
                                   match uu____12434 with
                                   | Success uu____12438 ->
                                       let wl1 =
                                         let uu___159_12440 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_12440.wl_deferred);
                                           ctr = (uu___159_12440.ctr);
                                           defer_ok =
                                             (uu___159_12440.defer_ok);
                                           smt_ok = (uu___159_12440.smt_ok);
                                           tcenv = (uu___159_12440.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____12442 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____12445 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____12446 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____12545 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____12545
                      then
                        let uu____12546 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____12546
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_12600 = hd1 in
                      let uu____12601 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_12600.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_12600.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12601
                      } in
                    let hd21 =
                      let uu___161_12607 = hd2 in
                      let uu____12608 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_12607.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_12607.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____12608
                      } in
                    let prob =
                      let uu____12614 =
                        let uu____12619 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____12619 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____12614 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____12632 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____12632 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____12636 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____12636 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____12668 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____12673 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____12668 uu____12673 in
                         ((let uu____12683 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____12683
                           then
                             let uu____12684 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____12685 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____12684 uu____12685
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____12712 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____12722 = aux scope env [] bs1 bs2 in
              match uu____12722 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____12746 = compress_tprob wl problem in
        solve_t' env uu____12746 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____12779 = head_matches_delta env1 wl1 t1 t2 in
          match uu____12779 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12810,uu____12811) ->
                   let may_relate head3 =
                     let uu____12836 =
                       let uu____12837 = FStar_Syntax_Util.un_uinst head3 in
                       uu____12837.FStar_Syntax_Syntax.n in
                     match uu____12836 with
                     | FStar_Syntax_Syntax.Tm_name uu____12842 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12843 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____12875 -> false in
                   let uu____12876 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12876
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
                                let uu____12897 =
                                  let uu____12898 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12898 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12897 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12900 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12900
                   else giveup env1 "head mismatch" orig
               | (uu____12902,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_12915 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_12915.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_12915.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_12915.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_12915.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_12915.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_12915.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_12915.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_12915.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12916,FStar_Pervasives_Native.None ) ->
                   ((let uu____12928 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12928
                     then
                       let uu____12929 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12930 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12931 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12932 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12929
                         uu____12930 uu____12931 uu____12932
                     else ());
                    (let uu____12934 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12934 with
                     | (head11,args1) ->
                         let uu____12983 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12983 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____13051 =
                                  let uu____13052 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____13053 = args_to_string args1 in
                                  let uu____13054 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____13055 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____13052 uu____13053 uu____13054
                                    uu____13055 in
                                giveup env1 uu____13051 orig
                              else
                                (let uu____13057 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____13060 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____13060 = FStar_Syntax_Util.Equal) in
                                 if uu____13057
                                 then
                                   let uu____13061 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____13061 with
                                   | USolved wl2 ->
                                       let uu____13063 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____13063
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____13067 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____13067 with
                                    | (base1,refinement1) ->
                                        let uu____13116 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____13116 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____13221 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____13221 with
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
                                                           (fun uu____13236 
                                                              ->
                                                              fun uu____13237
                                                                 ->
                                                                match 
                                                                  (uu____13236,
                                                                    uu____13237)
                                                                with
                                                                | ((a,uu____13255),
                                                                   (a',uu____13257))
                                                                    ->
                                                                    let uu____13266
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
                                                                    uu____13266)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____13276 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____13276 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____13281 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___163_13344 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_13344.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____13366 = p in
          match uu____13366 with
          | (((u,k),xs,c),ps,(h,uu____13377,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13459 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13459 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13482 = h gs_xs in
                     let uu____13483 =
                       let uu____13496 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50) in
                       FStar_All.pipe_right uu____13496
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51) in
                     FStar_Syntax_Util.abs xs1 uu____13482 uu____13483 in
                   ((let uu____13556 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13556
                     then
                       let uu____13557 =
                         FStar_Syntax_Print.binders_to_string ", " xs1 in
                       let uu____13558 = FStar_Syntax_Print.comp_to_string c in
                       let uu____13559 = FStar_Syntax_Print.term_to_string im in
                       let uu____13560 = FStar_Syntax_Print.tag_of_term im in
                       let uu____13561 =
                         let uu____13562 =
                           FStar_List.map (prob_to_string env1) sub_probs in
                         FStar_All.pipe_right uu____13562
                           (FStar_String.concat ", ") in
                       let uu____13567 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13557 uu____13558 uu____13559 uu____13560
                         uu____13561 uu____13567
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___129_13588 =
          match uu___129_13588 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13620 = p in
          match uu____13620 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13711 = FStar_List.nth ps i in
              (match uu____13711 with
               | (pi,uu____13715) ->
                   let uu____13724 = FStar_List.nth xs i in
                   (match uu____13724 with
                    | (xi,uu____13736) ->
                        let rec gs k =
                          let uu____13749 = FStar_Syntax_Util.arrow_formals k in
                          match uu____13749 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13842)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13855 = new_uvar r xs k_a in
                                    (match uu____13855 with
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
                                         let uu____13879 = aux subst2 tl1 in
                                         (match uu____13879 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13906 =
                                                let uu____13909 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13909 :: gi_xs' in
                                              let uu____13910 =
                                                let uu____13913 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13913 :: gi_ps' in
                                              (uu____13906, uu____13910))) in
                              aux [] bs in
                        let uu____13918 =
                          let uu____13919 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13919 in
                        if uu____13918
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13923 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13923 with
                           | (g_xs,uu____13935) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13946 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     FStar_Pervasives_Native.None r in
                                 let uu____13947 =
                                   let uu____13960 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52) in
                                   FStar_All.pipe_right uu____13960
                                     (fun _0_53  ->
                                        FStar_Pervasives_Native.Some _0_53) in
                                 FStar_Syntax_Util.abs xs uu____13946
                                   uu____13947 in
                               let sub1 =
                                 let uu____14020 =
                                   let uu____14025 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       FStar_Pervasives_Native.None r in
                                   let uu____14030 =
                                     let uu____14035 =
                                       FStar_List.map
                                         (fun uu____14046  ->
                                            match uu____14046 with
                                            | (uu____14055,uu____14056,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____14035 in
                                   mk_problem (p_scope orig) orig uu____14025
                                     (p_rel orig) uu____14030
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____14020 in
                               ((let uu____14073 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14073
                                 then
                                   let uu____14074 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____14075 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14074 uu____14075
                                 else ());
                                (let wl2 =
                                   let uu____14078 =
                                     let uu____14081 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____14081 in
                                   solve_prob orig uu____14078
                                     [TERM (u, proj)] wl1 in
                                 let uu____14090 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_55  ->
                                      FStar_Pervasives_Native.Some _0_55)
                                   uu____14090))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14121 = lhs in
          match uu____14121 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14157 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14157 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14190 =
                        let uu____14237 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14237) in
                      FStar_Pervasives_Native.Some uu____14190
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____14381 =
                           let uu____14388 =
                             let uu____14389 = FStar_Syntax_Subst.compress k in
                             uu____14389.FStar_Syntax_Syntax.n in
                           (uu____14388, args) in
                         match uu____14381 with
                         | (uu____14402,[]) ->
                             let uu____14405 =
                               let uu____14416 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____14416) in
                             FStar_Pervasives_Native.Some uu____14405
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14437,uu____14438) ->
                             let uu____14459 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____14459 with
                              | (uv1,uv_args) ->
                                  let uu____14514 =
                                    let uu____14515 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14515.FStar_Syntax_Syntax.n in
                                  (match uu____14514 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14527) ->
                                       let uu____14552 =
                                         pat_vars env [] uv_args in
                                       (match uu____14552 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14577  ->
                                                      let uu____14578 =
                                                        let uu____14579 =
                                                          let uu____14580 =
                                                            let uu____14585 =
                                                              let uu____14586
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14586
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14585 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14580 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____14579 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14578)) in
                                            let c1 =
                                              let uu____14596 =
                                                let uu____14597 =
                                                  let uu____14602 =
                                                    let uu____14603 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14603
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____14602 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14597 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14596 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14618 =
                                                let uu____14631 =
                                                  let uu____14642 =
                                                    let uu____14643 =
                                                      let uu____14648 =
                                                        let uu____14649 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____14649
                                                          FStar_Pervasives_Native.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____14648 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____14643 in
                                                  FStar_Util.Inl uu____14642 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14631 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14618 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14693 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14698,uu____14699) ->
                             let uu____14722 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____14722 with
                              | (uv1,uv_args) ->
                                  let uu____14777 =
                                    let uu____14778 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14778.FStar_Syntax_Syntax.n in
                                  (match uu____14777 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14790) ->
                                       let uu____14815 =
                                         pat_vars env [] uv_args in
                                       (match uu____14815 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14840  ->
                                                      let uu____14841 =
                                                        let uu____14842 =
                                                          let uu____14843 =
                                                            let uu____14848 =
                                                              let uu____14849
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14849
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14848 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14843 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____14842 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14841)) in
                                            let c1 =
                                              let uu____14859 =
                                                let uu____14860 =
                                                  let uu____14865 =
                                                    let uu____14866 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14866
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____14865 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14860 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14859 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14881 =
                                                let uu____14894 =
                                                  let uu____14905 =
                                                    let uu____14906 =
                                                      let uu____14911 =
                                                        let uu____14912 =
                                                          FStar_Syntax_Util.type_u
                                                            () in
                                                        FStar_All.pipe_right
                                                          uu____14912
                                                          FStar_Pervasives_Native.fst in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____14911 in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____14906 in
                                                  FStar_Util.Inl uu____14905 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14894 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14881 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14956 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14963) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____15004 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____15004
                                 (fun _0_56  ->
                                    FStar_Pervasives_Native.Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____15035 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____15035 with
                                  | (args1,rest) ->
                                      let uu____15062 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____15062 with
                                       | (xs2,c2) ->
                                           let uu____15075 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____15075
                                             (fun uu____15096  ->
                                                match uu____15096 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____15136 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____15136 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1)))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____15206 =
                                        let uu____15211 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15211 in
                                      FStar_All.pipe_right uu____15206
                                        (fun _0_57  ->
                                           FStar_Pervasives_Native.Some _0_57))
                         | uu____15226 ->
                             let uu____15233 =
                               let uu____15234 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____15241 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____15242 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____15234 uu____15241 uu____15242 in
                             failwith uu____15233 in
                       let uu____15249 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____15249
                         (fun uu____15300  ->
                            match uu____15300 with
                            | (xs1,c1) ->
                                let uu____15349 =
                                  let uu____15390 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____15390) in
                                FStar_Pervasives_Native.Some uu____15349)) in
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
                     let uu____15508 = imitate orig env wl1 st in
                     match uu____15508 with
                     | Failed uu____15513 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____15521 = project orig env wl1 i st in
                      match uu____15521 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____15529) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____15547 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15547 with
                | (hd1,uu____15567) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15596 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15611 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15612 -> true
                     | uu____15641 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15645 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15645
                         then true
                         else
                           ((let uu____15648 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15648
                             then
                               let uu____15649 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____15649
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____15658 =
                    let uu____15663 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____15663
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____15658 FStar_Syntax_Free.names in
                let uu____15724 = FStar_Util.set_is_empty fvs_hd in
                if uu____15724
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15735 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15735 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15748 =
                            let uu____15749 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15749 in
                          giveup_or_defer1 orig uu____15748
                        else
                          (let uu____15751 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15751
                           then
                             let uu____15752 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15752
                              then
                                let uu____15753 = subterms args_lhs in
                                imitate' orig env wl1 uu____15753
                              else
                                ((let uu____15758 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15758
                                  then
                                    let uu____15759 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15760 = names_to_string fvs1 in
                                    let uu____15761 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15759 uu____15760 uu____15761
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____15768 ->
                                        let uu____15769 = sn_binders env vars in
                                        u_abs k_uv uu____15769 t21 in
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
                               (let uu____15783 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15783
                                then
                                  ((let uu____15785 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15785
                                    then
                                      let uu____15786 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15787 = names_to_string fvs1 in
                                      let uu____15788 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____15786 uu____15787 uu____15788
                                    else ());
                                   (let uu____15790 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____15790 (- (Prims.parse_int "1"))))
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
                     (let uu____15803 =
                        let uu____15804 = FStar_Syntax_Free.names t1 in
                        check_head uu____15804 t2 in
                      if uu____15803
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____15809 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15809
                          then
                            let uu____15810 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____15810
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____15813 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____15813 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____15872 =
               match uu____15872 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____15928 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____15928 with
                    | (all_formals,uu____15948) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____16115  ->
                                        match uu____16115 with
                                        | (x,imp) ->
                                            let uu____16126 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____16126, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____16139 = FStar_Syntax_Util.type_u () in
                                match uu____16139 with
                                | (t1,uu____16145) ->
                                    let uu____16146 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____16146 in
                              let uu____16151 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____16151 with
                               | (t',tm_u1) ->
                                   let uu____16162 = destruct_flex_t t' in
                                   (match uu____16162 with
                                    | (uu____16201,u1,k11,uu____16204) ->
                                        let sol =
                                          let uu____16258 =
                                            let uu____16267 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____16267) in
                                          TERM uu____16258 in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1)
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____16373 = pat_var_opt env pat_args hd1 in
                              (match uu____16373 with
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
                                              (fun uu____16427  ->
                                                 match uu____16427 with
                                                 | (x,uu____16433) ->
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
                                      let uu____16442 =
                                        let uu____16443 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____16443 in
                                      if uu____16442
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____16449 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____16449 formals1
                                           tl1)))
                          | uu____16460 -> failwith "Impossible" in
                        let uu____16481 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____16481 all_formals args) in
             let solve_both_pats wl1 uu____16566 uu____16567 r =
               match (uu____16566, uu____16567) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____16865 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____16865
                   then
                     let uu____16872 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____16872
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____16896 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____16896
                       then
                         let uu____16897 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____16898 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____16899 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____16900 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____16901 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____16897 uu____16898 uu____16899 uu____16900
                           uu____16901
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____16963 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____16963 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16972 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____16972 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____17026 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____17026 in
                                  let uu____17031 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____17031 k3)
                           else
                             (let uu____17035 =
                                let uu____17036 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____17037 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____17038 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____17036 uu____17037 uu____17038 in
                              failwith uu____17035) in
                       let uu____17039 =
                         let uu____17050 =
                           let uu____17065 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____17065 in
                         match uu____17050 with
                         | (bs,k1') ->
                             let uu____17098 =
                               let uu____17113 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____17113 in
                             (match uu____17098 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____17149 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____17149 in
                                  let uu____17158 =
                                    let uu____17163 =
                                      let uu____17164 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____17164.FStar_Syntax_Syntax.n in
                                    let uu____17169 =
                                      let uu____17170 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____17170.FStar_Syntax_Syntax.n in
                                    (uu____17163, uu____17169) in
                                  (match uu____17158 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____17185,uu____17186) ->
                                       (k1', [sub_prob])
                                   | (uu____17193,FStar_Syntax_Syntax.Tm_type
                                      uu____17194) -> (k2', [sub_prob])
                                   | uu____17201 ->
                                       let uu____17206 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____17206 with
                                        | (t,uu____17222) ->
                                            let uu____17223 = new_uvar r zs t in
                                            (match uu____17223 with
                                             | (k_zs,uu____17239) ->
                                                 let kprob =
                                                   let uu____17241 =
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
                                                          _0_59) uu____17241 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____17039 with
                       | (k_u',sub_probs) ->
                           let uu____17266 =
                             let uu____17281 =
                               let uu____17282 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____17282 in
                             let uu____17291 =
                               let uu____17296 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____17296 in
                             let uu____17301 =
                               let uu____17306 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____17306 in
                             (uu____17281, uu____17291, uu____17301) in
                           (match uu____17266 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____17339 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____17339 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____17382 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____17382
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____17392 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____17392 with
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
             let solve_one_pat uu____17485 uu____17486 =
               match (uu____17485, uu____17486) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____17684 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____17684
                     then
                       let uu____17685 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____17686 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____17685 uu____17686
                     else ());
                    (let uu____17688 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____17688
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____17706  ->
                              fun uu____17707  ->
                                match (uu____17706, uu____17707) with
                                | ((a,uu____17725),(t21,uu____17727)) ->
                                    let uu____17736 =
                                      let uu____17741 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____17741
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____17736
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2 in
                       let guard =
                         let uu____17747 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____17747 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____17761 = occurs_check env wl (u1, k1) t21 in
                        match uu____17761 with
                        | (occurs_ok,uu____17777) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____17785 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____17785
                            then
                              let sol =
                                let uu____17787 =
                                  let uu____17796 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____17796) in
                                TERM uu____17787 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____17819 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____17819
                               then
                                 let uu____17820 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____17820 with
                                 | (sol,(uu____17846,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____17860 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____17860
                                       then
                                         let uu____17861 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____17861
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____17868 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____17870 = lhs in
             match uu____17870 with
             | (t1,u1,k1,args1) ->
                 let uu____17875 = rhs in
                 (match uu____17875 with
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
                       | uu____17915 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____17925 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____17925 with
                              | (sol,uu____17937) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____17940 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____17940
                                    then
                                      let uu____17941 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____17941
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____17948 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____17950 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____17950
        then
          let uu____17951 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____17951
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____17955 = FStar_Util.physical_equality t1 t2 in
           if uu____17955
           then
             let uu____17956 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____17956
           else
             ((let uu____17959 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____17959
               then
                 let uu____17960 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____17960
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____17963,uu____17964) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____17965,FStar_Syntax_Syntax.Tm_bvar uu____17966) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_18033 =
                     match uu___130_18033 with
                     | [] -> c
                     | bs ->
                         let uu____18059 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____18059 in
                   let uu____18070 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____18070 with
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
                                   let uu____18227 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____18227
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____18229 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____18229))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_18367 =
                     match uu___131_18367 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____18427 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____18427 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____18581 =
                                   let uu____18586 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____18587 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____18586
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____18587 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____18581))
               | (FStar_Syntax_Syntax.Tm_abs uu____18592,uu____18593) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____18634 -> true
                     | uu____18663 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____18711 =
                     let uu____18732 = maybe_eta t1 in
                     let uu____18741 = maybe_eta t2 in
                     (uu____18732, uu____18741) in
                   (match uu____18711 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_18800 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_18800.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_18800.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_18800.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_18800.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_18800.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_18800.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_18800.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_18800.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____18835 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____18835
                        then
                          let uu____18836 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____18836 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____18874 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____18874
                        then
                          let uu____18875 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____18875 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____18883 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____18904,FStar_Syntax_Syntax.Tm_abs uu____18905) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____18946 -> true
                     | uu____18975 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____19023 =
                     let uu____19044 = maybe_eta t1 in
                     let uu____19053 = maybe_eta t2 in
                     (uu____19044, uu____19053) in
                   (match uu____19023 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_19112 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_19112.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_19112.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_19112.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_19112.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_19112.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_19112.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_19112.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_19112.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____19147 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____19147
                        then
                          let uu____19148 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____19148 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____19186 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____19186
                        then
                          let uu____19187 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____19187 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____19195 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____19216,FStar_Syntax_Syntax.Tm_refine uu____19217) ->
                   let uu____19234 = as_refinement env wl t1 in
                   (match uu____19234 with
                    | (x1,phi1) ->
                        let uu____19241 = as_refinement env wl t2 in
                        (match uu____19241 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____19249 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____19249 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____19289 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____19289
                                 (guard_on_element wl problem x11) in
                             let fallback uu____19293 =
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
                                 let uu____19301 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____19301 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____19312 =
                                   let uu____19317 =
                                     let uu____19318 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____19318 :: (p_scope orig) in
                                   mk_problem uu____19317 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____19312 in
                               let uu____19323 =
                                 solve env1
                                   (let uu___165_19324 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_19324.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_19324.smt_ok);
                                      tcenv = (uu___165_19324.tcenv)
                                    }) in
                               (match uu____19323 with
                                | Failed uu____19331 -> fallback ()
                                | Success uu____19336 ->
                                    let guard =
                                      let uu____19342 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____19347 =
                                        let uu____19348 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____19348
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____19342
                                        uu____19347 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___166_19359 = wl1 in
                                      {
                                        attempting =
                                          (uu___166_19359.attempting);
                                        wl_deferred =
                                          (uu___166_19359.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_19359.defer_ok);
                                        smt_ok = (uu___166_19359.smt_ok);
                                        tcenv = (uu___166_19359.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19361,FStar_Syntax_Syntax.Tm_uvar uu____19362) ->
                   let uu____19395 = destruct_flex_t t1 in
                   let uu____19396 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19395 uu____19396
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19397;
                     FStar_Syntax_Syntax.tk = uu____19398;
                     FStar_Syntax_Syntax.pos = uu____19399;
                     FStar_Syntax_Syntax.vars = uu____19400;_},uu____19401),FStar_Syntax_Syntax.Tm_uvar
                  uu____19402) ->
                   let uu____19463 = destruct_flex_t t1 in
                   let uu____19464 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19463 uu____19464
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19465,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19466;
                     FStar_Syntax_Syntax.tk = uu____19467;
                     FStar_Syntax_Syntax.pos = uu____19468;
                     FStar_Syntax_Syntax.vars = uu____19469;_},uu____19470))
                   ->
                   let uu____19531 = destruct_flex_t t1 in
                   let uu____19532 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19531 uu____19532
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19533;
                     FStar_Syntax_Syntax.tk = uu____19534;
                     FStar_Syntax_Syntax.pos = uu____19535;
                     FStar_Syntax_Syntax.vars = uu____19536;_},uu____19537),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19538;
                     FStar_Syntax_Syntax.tk = uu____19539;
                     FStar_Syntax_Syntax.pos = uu____19540;
                     FStar_Syntax_Syntax.vars = uu____19541;_},uu____19542))
                   ->
                   let uu____19631 = destruct_flex_t t1 in
                   let uu____19632 = destruct_flex_t t2 in
                   flex_flex1 orig uu____19631 uu____19632
               | (FStar_Syntax_Syntax.Tm_uvar uu____19633,uu____19634) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____19651 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____19651 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19658;
                     FStar_Syntax_Syntax.tk = uu____19659;
                     FStar_Syntax_Syntax.pos = uu____19660;
                     FStar_Syntax_Syntax.vars = uu____19661;_},uu____19662),uu____19663)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____19708 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____19708 t2 wl
               | (uu____19715,FStar_Syntax_Syntax.Tm_uvar uu____19716) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____19733,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19734;
                     FStar_Syntax_Syntax.tk = uu____19735;
                     FStar_Syntax_Syntax.pos = uu____19736;
                     FStar_Syntax_Syntax.vars = uu____19737;_},uu____19738))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19783,FStar_Syntax_Syntax.Tm_type uu____19784) ->
                   solve_t' env
                     (let uu___167_19801 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_19801.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_19801.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_19801.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_19801.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_19801.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_19801.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_19801.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_19801.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_19801.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19802;
                     FStar_Syntax_Syntax.tk = uu____19803;
                     FStar_Syntax_Syntax.pos = uu____19804;
                     FStar_Syntax_Syntax.vars = uu____19805;_},uu____19806),FStar_Syntax_Syntax.Tm_type
                  uu____19807) ->
                   solve_t' env
                     (let uu___167_19852 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_19852.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_19852.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_19852.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_19852.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_19852.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_19852.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_19852.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_19852.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_19852.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____19853,FStar_Syntax_Syntax.Tm_arrow uu____19854) ->
                   solve_t' env
                     (let uu___167_19885 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_19885.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_19885.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_19885.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_19885.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_19885.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_19885.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_19885.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_19885.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_19885.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19886;
                     FStar_Syntax_Syntax.tk = uu____19887;
                     FStar_Syntax_Syntax.pos = uu____19888;
                     FStar_Syntax_Syntax.vars = uu____19889;_},uu____19890),FStar_Syntax_Syntax.Tm_arrow
                  uu____19891) ->
                   solve_t' env
                     (let uu___167_19950 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_19950.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_19950.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_19950.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_19950.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_19950.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_19950.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_19950.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_19950.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_19950.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____19951,uu____19952) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____19971 =
                        let uu____19972 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____19972 in
                      if uu____19971
                      then
                        let uu____19973 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_19978 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_19978.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_19978.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_19978.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_19978.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_19978.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_19978.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_19978.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_19978.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_19978.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____19979 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____19973 uu____19979 t2
                          wl
                      else
                        (let uu____19987 = base_and_refinement env wl t2 in
                         match uu____19987 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____20044 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_20049 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_20049.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_20049.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_20049.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_20049.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_20049.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_20049.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_20049.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_20049.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_20049.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____20050 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____20044
                                    uu____20050 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___170_20076 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_20076.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_20076.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____20079 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____20079 in
                                  let guard =
                                    let uu____20093 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____20093
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____20103;
                     FStar_Syntax_Syntax.tk = uu____20104;
                     FStar_Syntax_Syntax.pos = uu____20105;
                     FStar_Syntax_Syntax.vars = uu____20106;_},uu____20107),uu____20108)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____20155 =
                        let uu____20156 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____20156 in
                      if uu____20155
                      then
                        let uu____20157 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_20162 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_20162.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_20162.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_20162.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_20162.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_20162.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_20162.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_20162.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_20162.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_20162.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____20163 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____20157 uu____20163 t2
                          wl
                      else
                        (let uu____20171 = base_and_refinement env wl t2 in
                         match uu____20171 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____20228 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_20233 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_20233.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_20233.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_20233.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_20233.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_20233.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_20233.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_20233.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_20233.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_20233.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____20234 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____20228
                                    uu____20234 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___170_20260 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_20260.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_20260.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____20263 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____20263 in
                                  let guard =
                                    let uu____20277 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____20277
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____20287,FStar_Syntax_Syntax.Tm_uvar uu____20288) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____20306 = base_and_refinement env wl t1 in
                      match uu____20306 with
                      | (t_base,uu____20326) ->
                          solve_t env
                            (let uu___171_20355 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_20355.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_20355.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_20355.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_20355.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_20355.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_20355.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_20355.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_20355.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____20360,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____20361;
                     FStar_Syntax_Syntax.tk = uu____20362;
                     FStar_Syntax_Syntax.pos = uu____20363;
                     FStar_Syntax_Syntax.vars = uu____20364;_},uu____20365))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____20411 = base_and_refinement env wl t1 in
                      match uu____20411 with
                      | (t_base,uu____20431) ->
                          solve_t env
                            (let uu___171_20460 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_20460.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_20460.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_20460.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_20460.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_20460.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_20460.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_20460.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_20460.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____20465,uu____20466) ->
                   let t21 =
                     let uu____20480 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____20480 in
                   solve_t env
                     (let uu___172_20505 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_20505.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_20505.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_20505.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_20505.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_20505.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_20505.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_20505.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_20505.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_20505.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____20506,FStar_Syntax_Syntax.Tm_refine uu____20507) ->
                   let t11 =
                     let uu____20521 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____20521 in
                   solve_t env
                     (let uu___173_20546 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_20546.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_20546.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_20546.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_20546.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_20546.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_20546.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_20546.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_20546.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_20546.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____20551,uu____20552) ->
                   let head1 =
                     let uu____20588 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20588
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20648 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20648
                       FStar_Pervasives_Native.fst in
                   let uu____20703 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20703
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20718 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20718
                      then
                        let guard =
                          let uu____20730 =
                            let uu____20731 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20731 = FStar_Syntax_Util.Equal in
                          if uu____20730
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20735 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_71  ->
                                  FStar_Pervasives_Native.Some _0_71)
                               uu____20735) in
                        let uu____20738 = solve_prob orig guard [] wl in
                        solve env uu____20738
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____20741,uu____20742) ->
                   let head1 =
                     let uu____20756 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20756
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20816 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20816
                       FStar_Pervasives_Native.fst in
                   let uu____20871 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20871
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20886 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20886
                      then
                        let guard =
                          let uu____20898 =
                            let uu____20899 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20899 = FStar_Syntax_Util.Equal in
                          if uu____20898
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20903 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_72  ->
                                  FStar_Pervasives_Native.Some _0_72)
                               uu____20903) in
                        let uu____20906 = solve_prob orig guard [] wl in
                        solve env uu____20906
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____20909,uu____20910) ->
                   let head1 =
                     let uu____20916 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20916
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20976 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20976
                       FStar_Pervasives_Native.fst in
                   let uu____21031 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21031
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21046 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21046
                      then
                        let guard =
                          let uu____21058 =
                            let uu____21059 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21059 = FStar_Syntax_Util.Equal in
                          if uu____21058
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21063 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_73  ->
                                  FStar_Pervasives_Native.Some _0_73)
                               uu____21063) in
                        let uu____21066 = solve_prob orig guard [] wl in
                        solve env uu____21066
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____21069,uu____21070) ->
                   let head1 =
                     let uu____21076 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21076
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21136 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21136
                       FStar_Pervasives_Native.fst in
                   let uu____21191 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21191
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21206 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21206
                      then
                        let guard =
                          let uu____21218 =
                            let uu____21219 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21219 = FStar_Syntax_Util.Equal in
                          if uu____21218
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21223 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_74  ->
                                  FStar_Pervasives_Native.Some _0_74)
                               uu____21223) in
                        let uu____21226 = solve_prob orig guard [] wl in
                        solve env uu____21226
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____21229,uu____21230) ->
                   let head1 =
                     let uu____21236 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21236
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21296 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21296
                       FStar_Pervasives_Native.fst in
                   let uu____21351 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21351
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21366 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21366
                      then
                        let guard =
                          let uu____21378 =
                            let uu____21379 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21379 = FStar_Syntax_Util.Equal in
                          if uu____21378
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21383 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_75  ->
                                  FStar_Pervasives_Native.Some _0_75)
                               uu____21383) in
                        let uu____21386 = solve_prob orig guard [] wl in
                        solve env uu____21386
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____21389,uu____21390) ->
                   let head1 =
                     let uu____21414 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21414
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21474 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21474
                       FStar_Pervasives_Native.fst in
                   let uu____21529 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21529
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21544 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21544
                      then
                        let guard =
                          let uu____21556 =
                            let uu____21557 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21557 = FStar_Syntax_Util.Equal in
                          if uu____21556
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21561 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____21561) in
                        let uu____21564 = solve_prob orig guard [] wl in
                        solve env uu____21564
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____21567,FStar_Syntax_Syntax.Tm_match uu____21568) ->
                   let head1 =
                     let uu____21604 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21604
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21664 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21664
                       FStar_Pervasives_Native.fst in
                   let uu____21719 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21719
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21734 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21734
                      then
                        let guard =
                          let uu____21746 =
                            let uu____21747 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21747 = FStar_Syntax_Util.Equal in
                          if uu____21746
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21751 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____21751) in
                        let uu____21754 = solve_prob orig guard [] wl in
                        solve env uu____21754
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____21757,FStar_Syntax_Syntax.Tm_uinst uu____21758) ->
                   let head1 =
                     let uu____21772 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21772
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21832 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21832
                       FStar_Pervasives_Native.fst in
                   let uu____21887 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____21887
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____21902 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____21902
                      then
                        let guard =
                          let uu____21914 =
                            let uu____21915 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____21915 = FStar_Syntax_Util.Equal in
                          if uu____21914
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____21919 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____21919) in
                        let uu____21922 = solve_prob orig guard [] wl in
                        solve env uu____21922
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____21925,FStar_Syntax_Syntax.Tm_name uu____21926) ->
                   let head1 =
                     let uu____21932 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____21932
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____21992 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____21992
                       FStar_Pervasives_Native.fst in
                   let uu____22047 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____22047
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____22062 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____22062
                      then
                        let guard =
                          let uu____22074 =
                            let uu____22075 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____22075 = FStar_Syntax_Util.Equal in
                          if uu____22074
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____22079 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____22079) in
                        let uu____22082 = solve_prob orig guard [] wl in
                        solve env uu____22082
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____22085,FStar_Syntax_Syntax.Tm_constant uu____22086) ->
                   let head1 =
                     let uu____22092 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____22092
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____22152 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____22152
                       FStar_Pervasives_Native.fst in
                   let uu____22207 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____22207
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____22222 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____22222
                      then
                        let guard =
                          let uu____22234 =
                            let uu____22235 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____22235 = FStar_Syntax_Util.Equal in
                          if uu____22234
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____22239 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____22239) in
                        let uu____22242 = solve_prob orig guard [] wl in
                        solve env uu____22242
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____22245,FStar_Syntax_Syntax.Tm_fvar uu____22246) ->
                   let head1 =
                     let uu____22252 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____22252
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____22312 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____22312
                       FStar_Pervasives_Native.fst in
                   let uu____22367 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____22367
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____22382 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____22382
                      then
                        let guard =
                          let uu____22394 =
                            let uu____22395 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____22395 = FStar_Syntax_Util.Equal in
                          if uu____22394
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____22399 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____22399) in
                        let uu____22402 = solve_prob orig guard [] wl in
                        solve env uu____22402
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____22405,FStar_Syntax_Syntax.Tm_app uu____22406) ->
                   let head1 =
                     let uu____22430 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____22430
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____22490 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____22490
                       FStar_Pervasives_Native.fst in
                   let uu____22545 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____22545
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____22560 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____22560
                      then
                        let guard =
                          let uu____22572 =
                            let uu____22573 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____22573 = FStar_Syntax_Util.Equal in
                          if uu____22572
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____22577 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____22577) in
                        let uu____22580 = solve_prob orig guard [] wl in
                        solve env uu____22580
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____22584,uu____22585),uu____22586) ->
                   solve_t' env
                     (let uu___174_22643 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_22643.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_22643.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_22643.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_22643.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_22643.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_22643.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_22643.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_22643.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_22643.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____22648,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____22650,uu____22651)) ->
                   solve_t' env
                     (let uu___175_22708 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_22708.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_22708.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_22708.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_22708.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_22708.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_22708.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_22708.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_22708.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_22708.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____22709,uu____22710) ->
                   let uu____22725 =
                     let uu____22726 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22727 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22726
                       uu____22727 in
                   failwith uu____22725
               | (FStar_Syntax_Syntax.Tm_meta uu____22728,uu____22729) ->
                   let uu____22738 =
                     let uu____22739 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22740 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22739
                       uu____22740 in
                   failwith uu____22738
               | (FStar_Syntax_Syntax.Tm_delayed uu____22741,uu____22742) ->
                   let uu____22781 =
                     let uu____22782 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22783 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22782
                       uu____22783 in
                   failwith uu____22781
               | (uu____22784,FStar_Syntax_Syntax.Tm_meta uu____22785) ->
                   let uu____22794 =
                     let uu____22795 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22796 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22795
                       uu____22796 in
                   failwith uu____22794
               | (uu____22797,FStar_Syntax_Syntax.Tm_delayed uu____22798) ->
                   let uu____22837 =
                     let uu____22838 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22839 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22838
                       uu____22839 in
                   failwith uu____22837
               | (uu____22840,FStar_Syntax_Syntax.Tm_let uu____22841) ->
                   let uu____22856 =
                     let uu____22857 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____22858 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____22857
                       uu____22858 in
                   failwith uu____22856
               | uu____22859 -> giveup env "head tag mismatch" orig)))
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
          (let uu____22895 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____22895
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____22908  ->
                  fun uu____22909  ->
                    match (uu____22908, uu____22909) with
                    | ((a1,uu____22927),(a2,uu____22929)) ->
                        let uu____22938 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____22938)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             let uu____22948 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs in
             FStar_Syntax_Util.mk_conj_l uu____22948 in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
           solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____22971 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____22982)::[] -> wp1
              | uu____23007 ->
                  let uu____23018 =
                    let uu____23019 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____23019 in
                  failwith uu____23018 in
            let uu____23024 =
              let uu____23035 =
                let uu____23036 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____23036 in
              [uu____23035] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____23024;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____23037 = lift_c1 () in solve_eq uu____23037 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_23042  ->
                       match uu___132_23042 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____23043 -> false)) in
             let uu____23044 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____23090)::uu____23091,(wp2,uu____23093)::uu____23094)
                   -> (wp1, wp2)
               | uu____23175 ->
                   let uu____23200 =
                     let uu____23201 =
                       let uu____23206 =
                         let uu____23207 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____23208 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____23207 uu____23208 in
                       (uu____23206, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____23201 in
                   raise uu____23200 in
             match uu____23044 with
             | (wpc1,wpc2) ->
                 let uu____23239 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____23239
                 then
                   let uu____23244 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____23244 wl
                 else
                   (let uu____23250 =
                      let uu____23257 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____23257 in
                    match uu____23250 with
                    | (c2_decl,qualifiers) ->
                        let uu____23278 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____23278
                        then
                          let c1_repr =
                            let uu____23282 =
                              let uu____23283 =
                                let uu____23284 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____23284 in
                              let uu____23285 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23283 uu____23285 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____23282 in
                          let c2_repr =
                            let uu____23287 =
                              let uu____23288 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____23289 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____23288 uu____23289 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____23287 in
                          let prob =
                            let uu____23291 =
                              let uu____23296 =
                                let uu____23297 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____23298 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____23297
                                  uu____23298 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____23296 in
                            FStar_TypeChecker_Common.TProb uu____23291 in
                          let wl1 =
                            let uu____23300 =
                              let uu____23303 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____23303 in
                            solve_prob orig uu____23300 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____23312 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____23312
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____23314 =
                                     let uu____23319 =
                                       let uu____23320 =
                                         let uu____23339 =
                                           let uu____23340 =
                                             let uu____23341 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____23341] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____23340 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____23342 =
                                           let uu____23345 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____23346 =
                                             let uu____23349 =
                                               let uu____23350 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____23350 in
                                             [uu____23349] in
                                           uu____23345 :: uu____23346 in
                                         (uu____23339, uu____23342) in
                                       FStar_Syntax_Syntax.Tm_app uu____23320 in
                                     FStar_Syntax_Syntax.mk uu____23319 in
                                   uu____23314
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____23358 =
                                    let uu____23363 =
                                      let uu____23364 =
                                        let uu____23383 =
                                          let uu____23384 =
                                            let uu____23385 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____23385] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____23384 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____23386 =
                                          let uu____23389 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____23390 =
                                            let uu____23393 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____23394 =
                                              let uu____23397 =
                                                let uu____23398 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____23398 in
                                              [uu____23397] in
                                            uu____23393 :: uu____23394 in
                                          uu____23389 :: uu____23390 in
                                        (uu____23383, uu____23386) in
                                      FStar_Syntax_Syntax.Tm_app uu____23364 in
                                    FStar_Syntax_Syntax.mk uu____23363 in
                                  uu____23358
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r) in
                           let base_prob =
                             let uu____23406 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____23406 in
                           let wl1 =
                             let uu____23416 =
                               let uu____23419 =
                                 let uu____23424 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____23424 g in
                               FStar_All.pipe_left
                                 (fun _0_85  ->
                                    FStar_Pervasives_Native.Some _0_85)
                                 uu____23419 in
                             solve_prob orig uu____23416 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____23443 = FStar_Util.physical_equality c1 c2 in
        if uu____23443
        then
          let uu____23444 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____23444
        else
          ((let uu____23447 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____23447
            then
              let uu____23448 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____23449 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____23448
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____23449
            else ());
           (let uu____23451 =
              let uu____23456 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____23457 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____23456, uu____23457) in
            match uu____23451 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23461),FStar_Syntax_Syntax.Total
                    (t2,uu____23463)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____23488 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23488 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23493,FStar_Syntax_Syntax.Total uu____23494) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23516),FStar_Syntax_Syntax.Total
                    (t2,uu____23518)) ->
                     let uu____23543 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23543 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____23549),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23551)) ->
                     let uu____23576 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23576 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____23582),FStar_Syntax_Syntax.GTotal
                    (t2,uu____23584)) ->
                     let uu____23609 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____23609 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____23614,FStar_Syntax_Syntax.Comp uu____23615) ->
                     let uu____23626 =
                       let uu___176_23631 = problem in
                       let uu____23636 =
                         let uu____23637 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23637 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_23631.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23636;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_23631.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_23631.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_23631.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_23631.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_23631.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_23631.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_23631.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_23631.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23626 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____23638,FStar_Syntax_Syntax.Comp uu____23639) ->
                     let uu____23650 =
                       let uu___176_23655 = problem in
                       let uu____23660 =
                         let uu____23661 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23661 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_23655.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____23660;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_23655.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_23655.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_23655.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_23655.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_23655.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_23655.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_23655.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_23655.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23650 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23662,FStar_Syntax_Syntax.GTotal uu____23663) ->
                     let uu____23674 =
                       let uu___177_23679 = problem in
                       let uu____23684 =
                         let uu____23685 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23685 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_23679.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_23679.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_23679.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23684;
                         FStar_TypeChecker_Common.element =
                           (uu___177_23679.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_23679.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_23679.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_23679.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_23679.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_23679.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23674 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23686,FStar_Syntax_Syntax.Total uu____23687) ->
                     let uu____23698 =
                       let uu___177_23703 = problem in
                       let uu____23708 =
                         let uu____23709 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____23709 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_23703.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_23703.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_23703.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____23708;
                         FStar_TypeChecker_Common.element =
                           (uu___177_23703.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_23703.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_23703.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_23703.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_23703.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_23703.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____23698 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____23710,FStar_Syntax_Syntax.Comp uu____23711) ->
                     let uu____23712 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21))) in
                     if uu____23712
                     then
                       let uu____23713 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____23713 wl
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
                           (let uu____23725 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____23725
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____23727 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____23727 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____23730 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____23731 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____23731) in
                                if uu____23730
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
                                  (let uu____23734 =
                                     let uu____23735 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____23736 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____23735 uu____23736 in
                                   giveup env uu____23734 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____23741 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____23780  ->
              match uu____23780 with
              | (uu____23801,uu____23802,u,uu____23804,uu____23805,uu____23806)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____23741 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____23859 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____23859 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____23877 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____23900  ->
                match uu____23900 with
                | (u1,u2) ->
                    let uu____23907 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____23908 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____23907 uu____23908)) in
      FStar_All.pipe_right uu____23877 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____23925,[])) -> "{}"
      | uu____23950 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____23967 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____23967
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____23970 =
              FStar_List.map
                (fun uu____23977  ->
                   match uu____23977 with
                   | (uu____23982,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____23970 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____23987 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____23987 imps
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____24029 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____24029
    then
      let uu____24030 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let uu____24031 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____24030
        (rel_to_string rel) uu____24031
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
            let uu____24055 =
              let uu____24058 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_86  -> FStar_Pervasives_Native.Some _0_86)
                uu____24058 in
            FStar_Syntax_Syntax.new_bv uu____24055 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____24067 =
              let uu____24070 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_87  -> FStar_Pervasives_Native.Some _0_87)
                uu____24070 in
            let uu____24073 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____24067 uu____24073 in
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
          let uu____24103 = FStar_Options.eager_inference () in
          if uu____24103
          then
            let uu___178_24104 = probs in
            {
              attempting = (uu___178_24104.attempting);
              wl_deferred = (uu___178_24104.wl_deferred);
              ctr = (uu___178_24104.ctr);
              defer_ok = false;
              smt_ok = (uu___178_24104.smt_ok);
              tcenv = (uu___178_24104.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Unionfind.commit tx; FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____24116 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____24116
              then
                let uu____24117 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____24117
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
          ((let uu____24127 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____24127
            then
              let uu____24128 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____24128
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____24132 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____24132
             then
               let uu____24133 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____24133
             else ());
            (let f2 =
               let uu____24136 =
                 let uu____24137 = FStar_Syntax_Util.unmeta f1 in
                 uu____24137.FStar_Syntax_Syntax.n in
               match uu____24136 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____24143 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___179_24144 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_24144.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_24144.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_24144.FStar_TypeChecker_Env.implicits)
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
            let uu____24163 =
              let uu____24164 =
                let uu____24165 =
                  let uu____24166 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____24166
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____24165;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____24164 in
            FStar_All.pipe_left
              (fun _0_89  -> FStar_Pervasives_Native.Some _0_89) uu____24163
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____24213 =
        let uu____24214 =
          let uu____24215 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst in
          FStar_All.pipe_right uu____24215
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90) in
        {
          FStar_TypeChecker_Env.guard_f = uu____24214;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        } in
      FStar_Pervasives_Native.Some uu____24213
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
          (let uu____24253 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____24253
           then
             let uu____24254 = FStar_Syntax_Print.term_to_string t1 in
             let uu____24255 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____24254
               uu____24255
           else ());
          (let prob =
             let uu____24258 =
               let uu____24263 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____24263 in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____24258 in
           let g =
             let uu____24271 =
               let uu____24274 = singleton' env prob smt_ok in
               solve_and_commit env uu____24274
                 (fun uu____24275  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____24271 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____24293 = try_teq true env t1 t2 in
        match uu____24293 with
        | FStar_Pervasives_Native.None  ->
            let uu____24296 =
              let uu____24297 =
                let uu____24302 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____24303 = FStar_TypeChecker_Env.get_range env in
                (uu____24302, uu____24303) in
              FStar_Errors.Error uu____24297 in
            raise uu____24296
        | FStar_Pervasives_Native.Some g ->
            ((let uu____24306 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____24306
              then
                let uu____24307 = FStar_Syntax_Print.term_to_string t1 in
                let uu____24308 = FStar_Syntax_Print.term_to_string t2 in
                let uu____24309 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____24307
                  uu____24308 uu____24309
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
          (let uu____24326 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____24326
           then
             let uu____24327 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____24328 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____24327
               uu____24328
           else ());
          (let uu____24330 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____24330 with
           | (prob,x) ->
               let g =
                 let uu____24342 =
                   let uu____24345 = singleton' env prob smt_ok in
                   solve_and_commit env uu____24345
                     (fun uu____24346  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____24342 in
               ((let uu____24356 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____24356
                 then
                   let uu____24357 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____24358 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____24359 =
                     let uu____24360 = FStar_Util.must g in
                     guard_to_string env uu____24360 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____24357 uu____24358 uu____24359
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
          let uu____24385 = FStar_TypeChecker_Env.get_range env in
          let uu____24386 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____24385 uu____24386
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____24399 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____24399
         then
           let uu____24400 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____24401 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____24400
             uu____24401
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____24406 =
             let uu____24411 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____24411 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____24406 in
         let uu____24416 =
           let uu____24419 = singleton env prob in
           solve_and_commit env uu____24419
             (fun uu____24420  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____24416)
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
      fun uu____24449  ->
        match uu____24449 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____24488 =
                 let uu____24489 =
                   let uu____24494 =
                     let uu____24495 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____24496 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____24495 uu____24496 in
                   let uu____24497 = FStar_TypeChecker_Env.get_range env in
                   (uu____24494, uu____24497) in
                 FStar_Errors.Error uu____24489 in
               raise uu____24488) in
            let equiv v1 v' =
              let uu____24505 =
                let uu____24510 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____24511 = FStar_Syntax_Subst.compress_univ v' in
                (uu____24510, uu____24511) in
              match uu____24505 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____24524 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____24549 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____24549 with
                      | FStar_Syntax_Syntax.U_unif uu____24556 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____24576  ->
                                    match uu____24576 with
                                    | (u,v') ->
                                        let uu____24585 = equiv v1 v' in
                                        if uu____24585
                                        then
                                          let uu____24588 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____24588 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____24604 -> [])) in
            let uu____24609 =
              let wl =
                let uu___180_24613 = empty_worklist env in
                {
                  attempting = (uu___180_24613.attempting);
                  wl_deferred = (uu___180_24613.wl_deferred);
                  ctr = (uu___180_24613.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_24613.smt_ok);
                  tcenv = (uu___180_24613.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____24626  ->
                      match uu____24626 with
                      | (lb,v1) ->
                          let uu____24633 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____24633 with
                           | USolved wl1 -> ()
                           | uu____24635 -> fail lb v1))) in
            let rec check_ineq uu____24643 =
              match uu____24643 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____24652) -> true
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
                      uu____24669,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____24671,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____24678) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____24684,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____24691 -> false) in
            let uu____24696 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____24707  ->
                      match uu____24707 with
                      | (u,v1) ->
                          let uu____24714 = check_ineq (u, v1) in
                          if uu____24714
                          then true
                          else
                            ((let uu____24717 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____24717
                              then
                                let uu____24718 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____24719 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____24718
                                  uu____24719
                              else ());
                             false))) in
            if uu____24696
            then ()
            else
              ((let uu____24723 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____24723
                then
                  ((let uu____24725 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____24725);
                   FStar_Unionfind.rollback tx;
                   (let uu____24735 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____24735))
                else ());
               (let uu____24745 =
                  let uu____24746 =
                    let uu____24751 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____24751) in
                  FStar_Errors.Error uu____24746 in
                raise uu____24745))
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
      let fail uu____24799 =
        match uu____24799 with
        | (d,s) ->
            let msg = explain env d s in
            raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____24813 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____24813
       then
         let uu____24814 = wl_to_string wl in
         let uu____24815 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____24814 uu____24815
       else ());
      (let g1 =
         let uu____24830 = solve_and_commit env wl fail in
         match uu____24830 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___181_24843 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_24843.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_24843.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_24843.FStar_TypeChecker_Env.implicits)
             }
         | uu____24848 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_24852 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_24852.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_24852.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_24852.FStar_TypeChecker_Env.implicits)
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
            let uu___183_24884 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_24884.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_24884.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_24884.FStar_TypeChecker_Env.implicits)
            } in
          let uu____24885 =
            let uu____24886 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____24886 in
          if uu____24885
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____24894 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____24894
                   then
                     let uu____24895 = FStar_TypeChecker_Env.get_range env in
                     let uu____24896 =
                       let uu____24897 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____24897 in
                     FStar_Errors.diag uu____24895 uu____24896
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
                         ((let uu____24908 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____24908
                           then
                             let uu____24909 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____24910 =
                               let uu____24911 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____24911 in
                             FStar_Errors.diag uu____24909 uu____24910
                           else ());
                          (let vcs =
                             let uu____24920 = FStar_Options.use_tactics () in
                             if uu____24920
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)] in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____24946  ->
                                   match uu____24946 with
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
      let uu____24959 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____24959 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____24965 =
            let uu____24966 =
              let uu____24971 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____24971) in
            FStar_Errors.Error uu____24966 in
          raise uu____24965
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____24978 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____24978 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____25007 = FStar_Unionfind.find u in
      match uu____25007 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____25024 -> false in
    let rec until_fixpoint acc implicits =
      let uu____25046 = acc in
      match uu____25046 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____25132 = hd1 in
               (match uu____25132 with
                | (uu____25145,env,u,tm,k,r) ->
                    let uu____25151 = unresolved u in
                    if uu____25151
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm in
                       (let uu____25182 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck") in
                        if uu____25182
                        then
                          let uu____25183 =
                            FStar_Syntax_Print.uvar_to_string u in
                          let uu____25190 =
                            FStar_Syntax_Print.term_to_string tm1 in
                          let uu____25191 =
                            FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____25183 uu____25190 uu____25191
                        else ());
                       (let uu____25193 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_25200 = env1 in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_25200.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_25200.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_25200.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_25200.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_25200.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_25200.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_25200.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_25200.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_25200.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_25200.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_25200.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_25200.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_25200.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_25200.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_25200.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_25200.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_25200.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_25200.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_25200.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_25200.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_25200.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_25200.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_25200.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1 in
                        match uu____25193 with
                        | (uu____25201,uu____25202,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_25205 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_25205.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_25205.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_25205.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____25208 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____25213  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true in
                              match uu____25208 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
    let uu___186_25241 = g in
    let uu____25242 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_25241.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_25241.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_25241.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____25242
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____25290 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____25290 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____25303 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____25303
      | (reason,uu____25305,uu____25306,e,t,r)::uu____25310 ->
          let uu____25337 =
            let uu____25338 = FStar_Syntax_Print.term_to_string t in
            let uu____25339 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____25338 uu____25339 in
          FStar_Errors.err r uu____25337
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_25346 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_25346.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_25346.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_25346.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25372 = try_teq false env t1 t2 in
        match uu____25372 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____25376 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____25376 with
             | FStar_Pervasives_Native.Some uu____25381 -> true
             | FStar_Pervasives_Native.None  -> false)