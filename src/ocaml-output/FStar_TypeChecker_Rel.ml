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
        FStar_TypeChecker_Env.univ_ineqs = uu____33;
        FStar_TypeChecker_Env.implicits = uu____34;_} -> true
    | uu____61 -> false
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
            FStar_TypeChecker_Env.deferred = uu____98;
            FStar_TypeChecker_Env.univ_ineqs = uu____99;
            FStar_TypeChecker_Env.implicits = uu____100;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____126 -> failwith "impossible" in
          let uu____127 =
            let uu___159_128 = g1 in
            let uu____129 =
              let uu____130 =
                let uu____131 =
                  let uu____132 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____132] in
                FStar_Syntax_Util.abs uu____131 f
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
              FStar_All.pipe_left
                (fun _0_41  -> FStar_TypeChecker_Common.NonTrivial _0_41)
                uu____130 in
            {
              FStar_TypeChecker_Env.guard_f = uu____129;
              FStar_TypeChecker_Env.deferred =
                (uu___159_128.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___159_128.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___159_128.FStar_TypeChecker_Env.implicits)
            } in
          FStar_Pervasives_Native.Some uu____127
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___160_142 = g in
          let uu____143 =
            let uu____144 =
              let uu____145 =
                let uu____148 =
                  let uu____149 =
                    let uu____164 =
                      let uu____167 = FStar_Syntax_Syntax.as_arg e in
                      [uu____167] in
                    (f, uu____164) in
                  FStar_Syntax_Syntax.Tm_app uu____149 in
                FStar_Syntax_Syntax.mk uu____148 in
              uu____145 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_42  -> FStar_TypeChecker_Common.NonTrivial _0_42)
              uu____144 in
          {
            FStar_TypeChecker_Env.guard_f = uu____143;
            FStar_TypeChecker_Env.deferred =
              (uu___160_142.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___160_142.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___160_142.FStar_TypeChecker_Env.implicits)
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
          let uu___161_187 = g in
          let uu____188 =
            let uu____189 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____189 in
          {
            FStar_TypeChecker_Env.guard_f = uu____188;
            FStar_TypeChecker_Env.deferred =
              (uu___161_187.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___161_187.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___161_187.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____194 -> failwith "impossible"
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
          let uu____207 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____207
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____212 =
      let uu____213 = FStar_Syntax_Util.unmeta t in
      uu____213.FStar_Syntax_Syntax.n in
    match uu____212 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____217 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____253 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____253;
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
                       let uu____327 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____327
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___162_329 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___162_329.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___162_329.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___162_329.FStar_TypeChecker_Env.implicits)
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
               let uu____351 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____351
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
            let uu___163_367 = g in
            let uu____368 =
              let uu____369 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____369 in
            {
              FStar_TypeChecker_Env.guard_f = uu____368;
              FStar_TypeChecker_Env.deferred =
                (uu___163_367.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___163_367.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___163_367.FStar_TypeChecker_Env.implicits)
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
        let uv = FStar_Syntax_Unionfind.fresh () in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                FStar_Pervasives_Native.None r in
            (uv1, uv1)
        | uu____402 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____427 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____427 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____435 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____435, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____466 = FStar_Syntax_Util.type_u () in
        match uu____466 with
        | (t_type,u) ->
            let uu____473 =
              let uu____478 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____478 t_type in
            (match uu____473 with
             | (tt,uu____480) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____514 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____556 -> false
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
  tcenv: FStar_TypeChecker_Env.env;}[@@deriving show]
let __proj__Mkworklist__item__attempting:
  worklist -> FStar_TypeChecker_Common.probs =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
let __proj__Mkworklist__item__wl_deferred:
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
let __proj__Mkworklist__item__ctr: worklist -> Prims.int =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
let __proj__Mkworklist__item__defer_ok: worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
let __proj__Mkworklist__item__smt_ok: worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
let __proj__Mkworklist__item__tcenv: worklist -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
type solution =
  | Success of FStar_TypeChecker_Common.deferred
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Success: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____750 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____768 -> false
let __proj__Failed__item___0:
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT[@@deriving show]
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____793 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____798 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____803 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___131_827  ->
    match uu___131_827 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____834 =
        let uu____835 = FStar_Syntax_Subst.compress t in
        uu____835.FStar_Syntax_Syntax.n in
      match uu____834 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____864 = FStar_Syntax_Print.uvar_to_string u in
          let uu____865 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____864 uu____865
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____868;
             FStar_Syntax_Syntax.vars = uu____869;_},args)
          ->
          let uu____915 = FStar_Syntax_Print.uvar_to_string u in
          let uu____916 = FStar_Syntax_Print.term_to_string ty in
          let uu____917 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____915 uu____916 uu____917
      | uu____918 -> "--" in
    let uu____919 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____919 detail
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___132_927  ->
      match uu___132_927 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____933 =
            let uu____936 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____937 =
              let uu____940 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____941 =
                let uu____944 =
                  let uu____947 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____947] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____944 in
              uu____940 :: uu____941 in
            uu____936 :: uu____937 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____933
      | FStar_TypeChecker_Common.CProb p ->
          let uu____953 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____954 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____953
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____954
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___133_962  ->
      match uu___133_962 with
      | UNIV (u,t) ->
          let x =
            let uu____966 = FStar_Options.hide_uvar_nums () in
            if uu____966
            then "?"
            else
              (let uu____968 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____968 FStar_Util.string_of_int) in
          let uu____969 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____969
      | TERM ((u,uu____971),t) ->
          let x =
            let uu____978 = FStar_Options.hide_uvar_nums () in
            if uu____978
            then "?"
            else
              (let uu____980 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____980 FStar_Util.string_of_int) in
          let uu____981 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____981
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____994 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____994 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____1007 =
      let uu____1010 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1010
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1007 (FStar_String.concat ", ")
let args_to_string:
  'Auu____1023 .
    (FStar_Syntax_Syntax.term,'Auu____1023) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1040 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1058  ->
              match uu____1058 with
              | (x,uu____1064) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1040 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1071 =
      let uu____1072 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1072 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1071;
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
        let uu___164_1091 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___164_1091.wl_deferred);
          ctr = (uu___164_1091.ctr);
          defer_ok = (uu___164_1091.defer_ok);
          smt_ok;
          tcenv = (uu___164_1091.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1106 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1106,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___165_1127 = empty_worklist env in
      let uu____1128 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1128;
        wl_deferred = (uu___165_1127.wl_deferred);
        ctr = (uu___165_1127.ctr);
        defer_ok = false;
        smt_ok = (uu___165_1127.smt_ok);
        tcenv = (uu___165_1127.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___166_1145 = wl in
        {
          attempting = (uu___166_1145.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___166_1145.ctr);
          defer_ok = (uu___166_1145.defer_ok);
          smt_ok = (uu___166_1145.smt_ok);
          tcenv = (uu___166_1145.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___167_1164 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___167_1164.wl_deferred);
        ctr = (uu___167_1164.ctr);
        defer_ok = (uu___167_1164.defer_ok);
        smt_ok = (uu___167_1164.smt_ok);
        tcenv = (uu___167_1164.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1178 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1178
         then
           let uu____1179 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1179
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___134_1184  ->
    match uu___134_1184 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1191 'Auu____1192 .
    ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem ->
      ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___168_1209 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___168_1209.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___168_1209.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___168_1209.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___168_1209.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___168_1209.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___168_1209.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___168_1209.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1220 'Auu____1221 .
    ('Auu____1221,'Auu____1220) FStar_TypeChecker_Common.problem ->
      ('Auu____1221,'Auu____1220) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___135_1242  ->
    match uu___135_1242 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___136_1268  ->
      match uu___136_1268 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___137_1272  ->
    match uu___137_1272 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___138_1286  ->
    match uu___138_1286 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___139_1302  ->
    match uu___139_1302 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___140_1318  ->
    match uu___140_1318 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___141_1336  ->
    match uu___141_1336 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___142_1354  ->
    match uu___142_1354 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___143_1368  ->
    match uu___143_1368 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.TProb _0_45) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_46  -> FStar_TypeChecker_Common.CProb _0_46) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1391 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1391 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1404  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1505 'Auu____1506 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1506 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1506 ->
              'Auu____1505 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1506,'Auu____1505)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1543 = next_pid () in
                let uu____1544 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1543;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1544;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1567 'Auu____1568 .
    FStar_TypeChecker_Env.env ->
      'Auu____1568 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1568 ->
            'Auu____1567 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1568,'Auu____1567)
                    FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              fun reason  ->
                let scope = FStar_TypeChecker_Env.all_binders env in
                let uu____1606 = next_pid () in
                let uu____1607 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1606;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1607;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1628 'Auu____1629 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1629 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1629 ->
            'Auu____1628 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1629,'Auu____1628) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1662 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1662;
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
let guard_on_element:
  'Auu____1673 .
    worklist ->
      ('Auu____1673,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
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
        let uu____1726 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1726
        then
          let uu____1727 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1728 = prob_to_string env d in
          let uu____1729 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1727 uu____1728 uu____1729 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1735 -> failwith "impossible" in
           let uu____1736 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1750 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1751 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1750, uu____1751)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1757 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1758 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1757, uu____1758) in
           match uu____1736 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___144_1775  ->
            match uu___144_1775 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1787 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1789),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___145_1811  ->
           match uu___145_1811 with
           | UNIV uu____1814 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1820),t) ->
               let uu____1826 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1826
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___146_1848  ->
           match uu___146_1848 with
           | UNIV (u',t) ->
               let uu____1853 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1853
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1857 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1866 =
        let uu____1867 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1867 in
      FStar_Syntax_Subst.compress uu____1866
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1876 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1876
let norm_arg:
  'Auu____1883 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1883) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1883)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1904 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1904, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1937  ->
              match uu____1937 with
              | (x,imp) ->
                  let uu____1948 =
                    let uu___169_1949 = x in
                    let uu____1950 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___169_1949.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___169_1949.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1950
                    } in
                  (uu____1948, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1967 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1967
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1971 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1971
        | uu____1974 -> u2 in
      let uu____1975 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1975
let normalize_refinement:
  'Auu____1986 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____1986 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement:
  'Auu____2011 .
    FStar_TypeChecker_Env.env ->
      'Auu____2011 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                  FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
                                                                  FStar_Pervasives_Native.tuple2
                                                                  FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        let rec aux norm1 t11 =
          match t11.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2116 =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 match uu____2116 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2133;
                     FStar_Syntax_Syntax.vars = uu____2134;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2160 =
                       let uu____2161 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2162 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2161 uu____2162 in
                     failwith uu____2160)
          | FStar_Syntax_Syntax.Tm_uinst uu____2177 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2216 =
                   let uu____2217 = FStar_Syntax_Subst.compress t1' in
                   uu____2217.FStar_Syntax_Syntax.n in
                 match uu____2216 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2234 -> aux true t1'
                 | uu____2241 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2258 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2291 =
                   let uu____2292 = FStar_Syntax_Subst.compress t1' in
                   uu____2292.FStar_Syntax_Syntax.n in
                 match uu____2291 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2309 -> aux true t1'
                 | uu____2316 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2333 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2380 =
                   let uu____2381 = FStar_Syntax_Subst.compress t1' in
                   uu____2381.FStar_Syntax_Syntax.n in
                 match uu____2380 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2398 -> aux true t1'
                 | uu____2405 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2422 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2439 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2456 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2473 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2490 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2519 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2552 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2585 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2614 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2653 ->
              let uu____2660 =
                let uu____2661 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2662 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2661 uu____2662 in
              failwith uu____2660
          | FStar_Syntax_Syntax.Tm_ascribed uu____2677 ->
              let uu____2704 =
                let uu____2705 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2706 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2705 uu____2706 in
              failwith uu____2704
          | FStar_Syntax_Syntax.Tm_delayed uu____2721 ->
              let uu____2746 =
                let uu____2747 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2748 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2747 uu____2748 in
              failwith uu____2746
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2763 =
                let uu____2764 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2765 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2764 uu____2765 in
              failwith uu____2763 in
        let uu____2780 = whnf env t1 in aux false uu____2780
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2791 =
        let uu____2806 = empty_worklist env in
        base_and_refinement env uu____2806 t in
      FStar_All.pipe_right uu____2791 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2841 = FStar_Syntax_Syntax.null_bv t in
    (uu____2841, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2850 .
    FStar_TypeChecker_Env.env ->
      'Auu____2850 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2867 = base_and_refinement env wl t in
        match uu____2867 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let force_refinement:
  (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                              FStar_Pervasives_Native.tuple2
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun uu____2947  ->
    match uu____2947 with
    | (t_base,refopt) ->
        let uu____2974 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2974 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____3009 =
      let uu____3012 =
        let uu____3015 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3038  ->
                  match uu____3038 with | (uu____3045,uu____3046,x) -> x)) in
        FStar_List.append wl.attempting uu____3015 in
      FStar_List.map (wl_prob_to_string wl) uu____3012 in
    FStar_All.pipe_right uu____3009 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3074 =
          let uu____3093 =
            let uu____3094 = FStar_Syntax_Subst.compress k in
            uu____3094.FStar_Syntax_Syntax.n in
          match uu____3093 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3159 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3159)
              else
                (let uu____3185 = FStar_Syntax_Util.abs_formals t in
                 match uu____3185 with
                 | (ys',t1,uu____3214) ->
                     let uu____3219 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3219))
          | uu____3260 ->
              let uu____3261 =
                let uu____3272 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3272) in
              ((ys, t), uu____3261) in
        match uu____3074 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____3351 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3351 c in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
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
            let uu____3384 = p_guard prob in
            match uu____3384 with
            | (uu____3389,uv) ->
                ((let uu____3392 =
                    let uu____3393 = FStar_Syntax_Subst.compress uv in
                    uu____3393.FStar_Syntax_Syntax.n in
                  match uu____3392 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3425 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3425
                        then
                          let uu____3426 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3427 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3428 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3426
                            uu____3427 uu____3428
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3430 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___170_3433 = wl in
                  {
                    attempting = (uu___170_3433.attempting);
                    wl_deferred = (uu___170_3433.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___170_3433.defer_ok);
                    smt_ok = (uu___170_3433.smt_ok);
                    tcenv = (uu___170_3433.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3451 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3451
         then
           let uu____3452 = FStar_Util.string_of_int pid in
           let uu____3453 =
             let uu____3454 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3454 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3452 uu____3453
         else ());
        commit sol;
        (let uu___171_3461 = wl in
         {
           attempting = (uu___171_3461.attempting);
           wl_deferred = (uu___171_3461.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___171_3461.defer_ok);
           smt_ok = (uu___171_3461.smt_ok);
           tcenv = (uu___171_3461.tcenv)
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
            | (uu____3503,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3515 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3515 in
          (let uu____3521 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3521
           then
             let uu____3522 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3523 =
               let uu____3524 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3524 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3522 uu____3523
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs:
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3559 =
          let uu____3566 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3566 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3559
          (FStar_Util.for_some
             (fun uu____3602  ->
                match uu____3602 with
                | (uv,uu____3608) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3621 'Auu____3622 .
    'Auu____3622 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3621)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.typ ->
            (Prims.bool,Prims.string FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun t  ->
          let occurs_ok =
            let uu____3654 = occurs wl uk t in Prims.op_Negation uu____3654 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3661 =
                 let uu____3662 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3663 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3662 uu____3663 in
               FStar_Pervasives_Native.Some uu____3661) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3680 'Auu____3681 .
    'Auu____3681 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3680)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.bv FStar_Util.set ->
            FStar_Syntax_Syntax.term ->
              (Prims.bool,Prims.bool,(Prims.string
                                        FStar_Pervasives_Native.option,
                                       FStar_Syntax_Syntax.bv FStar_Util.set,
                                       FStar_Syntax_Syntax.bv FStar_Util.set)
                                       FStar_Pervasives_Native.tuple3)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun fvs  ->
          fun t  ->
            let fvs_t = FStar_Syntax_Free.names t in
            let uu____3735 = occurs_check env wl uk t in
            match uu____3735 with
            | (occurs_ok,msg) ->
                let uu____3766 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3766, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3793 'Auu____3794 .
    (FStar_Syntax_Syntax.bv,'Auu____3794) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3793) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3793) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun v1  ->
    fun v2  ->
      let as_set1 v3 =
        FStar_All.pipe_right v3
          (FStar_List.fold_left
             (fun out  ->
                fun x  ->
                  FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
             FStar_Syntax_Syntax.no_names) in
      let v1_set = as_set1 v1 in
      let uu____3878 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3932  ->
                fun uu____3933  ->
                  match (uu____3932, uu____3933) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4014 =
                        let uu____4015 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____4015 in
                      if uu____4014
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4040 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4040
                         then
                           let uu____4053 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4053)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3878 with | (isect,uu____4094) -> FStar_List.rev isect
let binders_eq:
  'Auu____4123 'Auu____4124 .
    (FStar_Syntax_Syntax.bv,'Auu____4124) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4123) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4179  ->
              fun uu____4180  ->
                match (uu____4179, uu____4180) with
                | ((a,uu____4198),(b,uu____4200)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4219 'Auu____4220 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4220) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4219)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4219)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4271 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4285  ->
                      match uu____4285 with
                      | (b,uu____4291) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4271
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4307 -> FStar_Pervasives_Native.None
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
            let uu____4382 = pat_var_opt env seen hd1 in
            (match uu____4382 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4396 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4396
                   then
                     let uu____4397 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4397
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4416 =
      let uu____4417 = FStar_Syntax_Subst.compress t in
      uu____4417.FStar_Syntax_Syntax.n in
    match uu____4416 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4420 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4437;
           FStar_Syntax_Syntax.pos = uu____4438;
           FStar_Syntax_Syntax.vars = uu____4439;_},uu____4440)
        -> true
    | uu____4477 -> false
let destruct_flex_t:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                             FStar_Syntax_Syntax.syntax
                                                             FStar_Pervasives_Native.option
                                                             FStar_Unionfind.p_uvar,
                                                            FStar_Syntax_Syntax.version)
                                                            FStar_Pervasives_Native.tuple2,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                              FStar_Syntax_Syntax.syntax,
                                                             FStar_Syntax_Syntax.aqual)
                                                             FStar_Pervasives_Native.tuple2
                                                             Prims.list)
      FStar_Pervasives_Native.tuple4
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
           FStar_Syntax_Syntax.pos = uu____4602;
           FStar_Syntax_Syntax.vars = uu____4603;_},args)
        -> (t, uv, k, args)
    | uu____4671 -> failwith "Not a flex-uvar"
let destruct_flex_pattern:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                                FStar_Syntax_Syntax.syntax
                                                                FStar_Pervasives_Native.option
                                                                FStar_Unionfind.p_uvar,
                                                               FStar_Syntax_Syntax.version)
                                                               FStar_Pervasives_Native.tuple2,
         FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax,
                                                                FStar_Syntax_Syntax.aqual)
                                                                FStar_Pervasives_Native.tuple2
                                                                Prims.list)
         FStar_Pervasives_Native.tuple4,FStar_Syntax_Syntax.binders
                                          FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____4750 = destruct_flex_t t in
      match uu____4750 with
      | (t1,uv,k,args) ->
          let uu____4865 = pat_vars env [] args in
          (match uu____4865 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4963 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5045 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5082 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5087 -> false
let head_match: match_result -> match_result =
  fun uu___147_5091  ->
    match uu___147_5091 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5106 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5117 ->
          let uu____5118 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5118 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5129 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5150 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5159 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5186 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5187 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5188 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5205 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5218 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5242) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5248,uu____5249) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5291) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5312;
             FStar_Syntax_Syntax.index = uu____5313;
             FStar_Syntax_Syntax.sort = t2;_},uu____5315)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5322 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5323 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5324 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5337 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5355 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5355
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
            let uu____5379 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5379
            then FullMatch
            else
              (let uu____5381 =
                 let uu____5390 =
                   let uu____5393 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5393 in
                 let uu____5394 =
                   let uu____5397 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5397 in
                 (uu____5390, uu____5394) in
               MisMatch uu____5381)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5403),FStar_Syntax_Syntax.Tm_uinst (g,uu____5405)) ->
            let uu____5414 = head_matches env f g in
            FStar_All.pipe_right uu____5414 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5423),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5425)) ->
            let uu____5474 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5474
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5481),FStar_Syntax_Syntax.Tm_refine (y,uu____5483)) ->
            let uu____5492 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5492 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5494),uu____5495) ->
            let uu____5500 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5500 head_match
        | (uu____5501,FStar_Syntax_Syntax.Tm_refine (x,uu____5503)) ->
            let uu____5508 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5508 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5509,FStar_Syntax_Syntax.Tm_type
           uu____5510) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5511,FStar_Syntax_Syntax.Tm_arrow uu____5512) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5538),FStar_Syntax_Syntax.Tm_app (head',uu____5540))
            ->
            let uu____5581 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5581 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5583),uu____5584) ->
            let uu____5605 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5605 head_match
        | (uu____5606,FStar_Syntax_Syntax.Tm_app (head1,uu____5608)) ->
            let uu____5629 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5629 head_match
        | uu____5630 ->
            let uu____5635 =
              let uu____5644 = delta_depth_of_term env t11 in
              let uu____5647 = delta_depth_of_term env t21 in
              (uu____5644, uu____5647) in
            MisMatch uu____5635
let head_matches_delta:
  'Auu____5664 .
    FStar_TypeChecker_Env.env ->
      'Auu____5664 ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                            FStar_Pervasives_Native.tuple2
                            FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let uu____5697 = FStar_Syntax_Util.head_and_args t in
            match uu____5697 with
            | (head1,uu____5715) ->
                let uu____5736 =
                  let uu____5737 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5737.FStar_Syntax_Syntax.n in
                (match uu____5736 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5743 =
                       let uu____5744 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5744 FStar_Option.isSome in
                     if uu____5743
                     then
                       let uu____5763 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5763
                         (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                     else FStar_Pervasives_Native.None
                 | uu____5767 -> FStar_Pervasives_Native.None) in
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
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5870)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5888 =
                     let uu____5897 = maybe_inline t11 in
                     let uu____5900 = maybe_inline t21 in
                     (uu____5897, uu____5900) in
                   match uu____5888 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail r
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.None ) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (uu____5937,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5955 =
                     let uu____5964 = maybe_inline t11 in
                     let uu____5967 = maybe_inline t21 in
                     (uu____5964, uu____5967) in
                   match uu____5955 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail r
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.None ) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                when d1 = d2 ->
                let uu____6010 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____6010 with
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
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
                let uu____6033 =
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
                     (t11, t2')) in
                (match uu____6033 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6057 -> fail r
            | uu____6066 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6100 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6138 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___148_6152  ->
    match uu___148_6152 with
    | T (t,uu____6154) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6172 = FStar_Syntax_Util.type_u () in
      match uu____6172 with
      | (t,uu____6178) ->
          let uu____6179 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6179
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6192 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6192 FStar_Pervasives_Native.fst
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
        let uu____6258 = head_matches env t1 t' in
        match uu____6258 with
        | MisMatch uu____6259 -> false
        | uu____6268 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6364,imp),T (t2,uu____6367)) -> (t2, imp)
                     | uu____6386 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6453  ->
                    match uu____6453 with
                    | (t2,uu____6467) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6510 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6510 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6585))::tcs2) ->
                       aux
                         (((let uu___172_6620 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___172_6620.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___172_6620.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6638 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___149_6691 =
                 match uu___149_6691 with
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
               let uu____6808 = decompose1 [] bs1 in
               (rebuild, matches, uu____6808))
      | uu____6857 ->
          let rebuild uu___150_6863 =
            match uu___150_6863 with
            | [] -> t1
            | uu____6866 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___151_6898  ->
    match uu___151_6898 with
    | T (t,uu____6900) -> t
    | uu____6909 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___152_6913  ->
    match uu___152_6913 with
    | T (t,uu____6915) -> FStar_Syntax_Syntax.as_arg t
    | uu____6924 -> failwith "Impossible"
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
              | (uu____7035,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7060 = new_uvar r scope1 k in
                  (match uu____7060 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7078 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7095 =
                         let uu____7096 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_48  ->
                              FStar_TypeChecker_Common.TProb _0_48)
                           uu____7096 in
                       ((T (gi_xs, mk_kind)), uu____7095))
              | (uu____7109,uu____7110,C uu____7111) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7258 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7275;
                         FStar_Syntax_Syntax.vars = uu____7276;_})
                        ->
                        let uu____7299 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7299 with
                         | (T (gi_xs,uu____7323),prob) ->
                             let uu____7333 =
                               let uu____7334 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_49  -> C _0_49)
                                 uu____7334 in
                             (uu____7333, [prob])
                         | uu____7337 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7352;
                         FStar_Syntax_Syntax.vars = uu____7353;_})
                        ->
                        let uu____7376 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7376 with
                         | (T (gi_xs,uu____7400),prob) ->
                             let uu____7410 =
                               let uu____7411 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____7411 in
                             (uu____7410, [prob])
                         | uu____7414 -> failwith "impossible")
                    | (uu____7425,uu____7426,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7428;
                         FStar_Syntax_Syntax.vars = uu____7429;_})
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
                        let uu____7560 =
                          let uu____7569 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7569 FStar_List.unzip in
                        (match uu____7560 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7623 =
                                 let uu____7624 =
                                   let uu____7627 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7627 un_T in
                                 let uu____7628 =
                                   let uu____7637 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7637
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7624;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7628;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7623 in
                             ((C gi_xs), sub_probs))
                    | uu____7646 ->
                        let uu____7659 = sub_prob scope1 args q in
                        (match uu____7659 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7258 with
                   | (tc,probs) ->
                       let uu____7690 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7753,uu____7754),T
                            (t,uu____7756)) ->
                             let b1 =
                               ((let uu___173_7793 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___173_7793.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___173_7793.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7794 =
                               let uu____7801 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7801 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7794)
                         | uu____7836 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7690 with
                        | (bopt,scope2,args1) ->
                            let uu____7920 = aux scope2 args1 qs2 in
                            (match uu____7920 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7957 =
                                         let uu____7960 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7960 in
                                       FStar_Syntax_Util.mk_conj_l uu____7957
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7983 =
                                         let uu____7986 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7987 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7986 :: uu____7987 in
                                       FStar_Syntax_Util.mk_conj_l uu____7983 in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
            aux scope ps qs
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ,
    FStar_Syntax_Syntax.args) FStar_Pervasives_Native.tuple4[@@deriving show]
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
    FStar_Pervasives_Native.tuple3[@@deriving show]
let rigid_rigid: Prims.int = Prims.parse_int "0"
let flex_rigid_eq: Prims.int = Prims.parse_int "1"
let flex_refine_inner: Prims.int = Prims.parse_int "2"
let flex_refine: Prims.int = Prims.parse_int "3"
let flex_rigid: Prims.int = Prims.parse_int "4"
let rigid_flex: Prims.int = Prims.parse_int "5"
let refine_flex: Prims.int = Prims.parse_int "6"
let flex_flex: Prims.int = Prims.parse_int "7"
let compress_tprob:
  'Auu____8058 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8058)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8058)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___174_8079 = p in
      let uu____8084 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8085 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___174_8079.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8084;
        FStar_TypeChecker_Common.relation =
          (uu___174_8079.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8085;
        FStar_TypeChecker_Common.element =
          (uu___174_8079.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___174_8079.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___174_8079.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___174_8079.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___174_8079.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___174_8079.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8099 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8099
            (fun _0_51  -> FStar_TypeChecker_Common.TProb _0_51)
      | FStar_TypeChecker_Common.CProb uu____8108 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8130 = compress_prob wl pr in
        FStar_All.pipe_right uu____8130 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8140 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8140 with
           | (lh,uu____8160) ->
               let uu____8181 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8181 with
                | (rh,uu____8201) ->
                    let uu____8222 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8239,FStar_Syntax_Syntax.Tm_uvar uu____8240)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8277,uu____8278)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8299,FStar_Syntax_Syntax.Tm_uvar uu____8300)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8321,uu____8322)
                          ->
                          let uu____8339 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8339 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8402 ->
                                    let rank =
                                      let uu____8412 = is_top_level_prob prob in
                                      if uu____8412
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8414 =
                                      let uu___175_8419 = tp in
                                      let uu____8424 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___175_8419.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___175_8419.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___175_8419.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8424;
                                        FStar_TypeChecker_Common.element =
                                          (uu___175_8419.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___175_8419.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___175_8419.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___175_8419.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___175_8419.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___175_8419.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8414)))
                      | (uu____8439,FStar_Syntax_Syntax.Tm_uvar uu____8440)
                          ->
                          let uu____8457 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8457 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8520 ->
                                    let uu____8529 =
                                      let uu___176_8536 = tp in
                                      let uu____8541 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___176_8536.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8541;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___176_8536.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___176_8536.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___176_8536.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___176_8536.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___176_8536.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___176_8536.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___176_8536.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___176_8536.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8529)))
                      | (uu____8562,uu____8563) -> (rigid_rigid, tp) in
                    (match uu____8222 with
                     | (rank,tp1) ->
                         let uu____8582 =
                           FStar_All.pipe_right
                             (let uu___177_8588 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___177_8588.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___177_8588.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___177_8588.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___177_8588.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___177_8588.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___177_8588.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___177_8588.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___177_8588.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___177_8588.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_52  ->
                                FStar_TypeChecker_Common.TProb _0_52) in
                         (rank, uu____8582))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8598 =
            FStar_All.pipe_right
              (let uu___178_8604 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___178_8604.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___178_8604.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___178_8604.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___178_8604.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___178_8604.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___178_8604.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___178_8604.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___178_8604.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___178_8604.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_53  -> FStar_TypeChecker_Common.CProb _0_53) in
          (rigid_rigid, uu____8598)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8660 probs =
      match uu____8660 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8713 = rank wl hd1 in
               (match uu____8713 with
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
  | UFailed of Prims.string[@@deriving show]
let uu___is_UDeferred: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8823 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8837 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8851 -> false
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
                        let uu____8896 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8896 with
                        | (k,uu____8902) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8912 -> false)))
            | uu____8913 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8964 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8964 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8967 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8977 =
                     let uu____8978 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8979 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8978
                       uu____8979 in
                   UFailed uu____8977)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8999 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8999 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9021 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9021 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____9024 ->
                let uu____9029 =
                  let uu____9030 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____9031 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9030
                    uu____9031 msg in
                UFailed uu____9029 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9032,uu____9033) ->
              let uu____9034 =
                let uu____9035 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9036 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9035 uu____9036 in
              failwith uu____9034
          | (FStar_Syntax_Syntax.U_unknown ,uu____9037) ->
              let uu____9038 =
                let uu____9039 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9040 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9039 uu____9040 in
              failwith uu____9038
          | (uu____9041,FStar_Syntax_Syntax.U_bvar uu____9042) ->
              let uu____9043 =
                let uu____9044 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9045 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9044 uu____9045 in
              failwith uu____9043
          | (uu____9046,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9047 =
                let uu____9048 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9049 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9048 uu____9049 in
              failwith uu____9047
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9073 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9073
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9095 = occurs_univ v1 u3 in
              if uu____9095
              then
                let uu____9096 =
                  let uu____9097 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9098 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9097 uu____9098 in
                try_umax_components u11 u21 uu____9096
              else
                (let uu____9100 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9100)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9120 = occurs_univ v1 u3 in
              if uu____9120
              then
                let uu____9121 =
                  let uu____9122 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9123 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9122 uu____9123 in
                try_umax_components u11 u21 uu____9121
              else
                (let uu____9125 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9125)
          | (FStar_Syntax_Syntax.U_max uu____9134,uu____9135) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9141 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9141
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9143,FStar_Syntax_Syntax.U_max uu____9144) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9150 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9150
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9152,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9153,FStar_Syntax_Syntax.U_name
             uu____9154) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9155) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9156) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9157,FStar_Syntax_Syntax.U_succ
             uu____9158) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9159,FStar_Syntax_Syntax.U_zero
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
let match_num_binders:
  'a 'b .
    ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list,'b) FStar_Pervasives_Native.tuple2,('a Prims.list,
                                                             'b)
                                                             FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun bc1  ->
    fun bc2  ->
      let uu____9253 = bc1 in
      match uu____9253 with
      | (bs1,mk_cod1) ->
          let uu____9294 = bc2 in
          (match uu____9294 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9364 = FStar_Util.first_N n1 bs in
                 match uu____9364 with
                 | (bs3,rest) ->
                     let uu____9389 = mk_cod rest in (bs3, uu____9389) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9418 =
                   let uu____9425 = mk_cod1 [] in (bs1, uu____9425) in
                 let uu____9428 =
                   let uu____9435 = mk_cod2 [] in (bs2, uu____9435) in
                 (uu____9418, uu____9428)
               else
                 if l1 > l2
                 then
                   (let uu____9477 = curry l2 bs1 mk_cod1 in
                    let uu____9490 =
                      let uu____9497 = mk_cod2 [] in (bs2, uu____9497) in
                    (uu____9477, uu____9490))
                 else
                   (let uu____9513 =
                      let uu____9520 = mk_cod1 [] in (bs1, uu____9520) in
                    let uu____9523 = curry l1 bs2 mk_cod2 in
                    (uu____9513, uu____9523)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9644 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9644
       then
         let uu____9645 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9645
       else ());
      (let uu____9647 = next_prob probs in
       match uu____9647 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___179_9668 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___179_9668.wl_deferred);
               ctr = (uu___179_9668.ctr);
               defer_ok = (uu___179_9668.defer_ok);
               smt_ok = (uu___179_9668.smt_ok);
               tcenv = (uu___179_9668.tcenv)
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
                  let uu____9679 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9679 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9684 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9684 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9689,uu____9690) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9707 ->
                let uu____9716 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9775  ->
                          match uu____9775 with
                          | (c,uu____9783,uu____9784) -> c < probs.ctr)) in
                (match uu____9716 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9825 =
                            FStar_List.map
                              (fun uu____9840  ->
                                 match uu____9840 with
                                 | (uu____9851,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9825
                      | uu____9854 ->
                          let uu____9863 =
                            let uu___180_9864 = probs in
                            let uu____9865 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9886  ->
                                      match uu____9886 with
                                      | (uu____9893,uu____9894,y) -> y)) in
                            {
                              attempting = uu____9865;
                              wl_deferred = rest;
                              ctr = (uu___180_9864.ctr);
                              defer_ok = (uu___180_9864.defer_ok);
                              smt_ok = (uu___180_9864.smt_ok);
                              tcenv = (uu___180_9864.tcenv)
                            } in
                          solve env uu____9863))))
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
            let uu____9901 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9901 with
            | USolved wl1 ->
                let uu____9903 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9903
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
                  let uu____9949 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9949 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9952 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9964;
                  FStar_Syntax_Syntax.vars = uu____9965;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9968;
                  FStar_Syntax_Syntax.vars = uu____9969;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9983,uu____9984) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9991,FStar_Syntax_Syntax.Tm_uinst uu____9992) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9999 -> USolved wl
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
            ((let uu____10009 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____10009
              then
                let uu____10010 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10010 msg
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
        (let uu____10019 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10019
         then
           let uu____10020 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10020
         else ());
        (let uu____10022 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____10022 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10084 = head_matches_delta env () t1 t2 in
               match uu____10084 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10125 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10174 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10189 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10190 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10189, uu____10190)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10195 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10196 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10195, uu____10196) in
                        (match uu____10174 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10222 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_54  ->
                                    FStar_TypeChecker_Common.TProb _0_54)
                                 uu____10222 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10253 =
                                    let uu____10262 =
                                      let uu____10265 =
                                        let uu____10268 =
                                          let uu____10269 =
                                            let uu____10276 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10276) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10269 in
                                        FStar_Syntax_Syntax.mk uu____10268 in
                                      uu____10265
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10284 =
                                      let uu____10287 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10287] in
                                    (uu____10262, uu____10284) in
                                  FStar_Pervasives_Native.Some uu____10253
                              | (uu____10300,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10302)) ->
                                  let uu____10307 =
                                    let uu____10314 =
                                      let uu____10317 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10317] in
                                    (t11, uu____10314) in
                                  FStar_Pervasives_Native.Some uu____10307
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10327),uu____10328) ->
                                  let uu____10333 =
                                    let uu____10340 =
                                      let uu____10343 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10343] in
                                    (t21, uu____10340) in
                                  FStar_Pervasives_Native.Some uu____10333
                              | uu____10352 ->
                                  let uu____10357 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10357 with
                                   | (head1,uu____10381) ->
                                       let uu____10402 =
                                         let uu____10403 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10403.FStar_Syntax_Syntax.n in
                                       (match uu____10402 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10414;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10416;_}
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
                                        | uu____10423 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10436) ->
                  let uu____10461 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___153_10487  ->
                            match uu___153_10487 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10494 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10494 with
                                      | (u',uu____10510) ->
                                          let uu____10531 =
                                            let uu____10532 = whnf env u' in
                                            uu____10532.FStar_Syntax_Syntax.n in
                                          (match uu____10531 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10536) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10561 -> false))
                                 | uu____10562 -> false)
                            | uu____10565 -> false)) in
                  (match uu____10461 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10599 tps =
                         match uu____10599 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10647 =
                                    let uu____10656 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10656 in
                                  (match uu____10647 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10691 -> FStar_Pervasives_Native.None) in
                       let uu____10700 =
                         let uu____10709 =
                           let uu____10716 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10716, []) in
                         make_lower_bound uu____10709 lower_bounds in
                       (match uu____10700 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10728 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10728
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
                            ((let uu____10748 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10748
                              then
                                let wl' =
                                  let uu___181_10750 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___181_10750.wl_deferred);
                                    ctr = (uu___181_10750.ctr);
                                    defer_ok = (uu___181_10750.defer_ok);
                                    smt_ok = (uu___181_10750.smt_ok);
                                    tcenv = (uu___181_10750.tcenv)
                                  } in
                                let uu____10751 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10751
                              else ());
                             (let uu____10753 =
                                solve_t env eq_prob
                                  (let uu___182_10755 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___182_10755.wl_deferred);
                                     ctr = (uu___182_10755.ctr);
                                     defer_ok = (uu___182_10755.defer_ok);
                                     smt_ok = (uu___182_10755.smt_ok);
                                     tcenv = (uu___182_10755.tcenv)
                                   }) in
                              match uu____10753 with
                              | Success uu____10758 ->
                                  let wl1 =
                                    let uu___183_10760 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___183_10760.wl_deferred);
                                      ctr = (uu___183_10760.ctr);
                                      defer_ok = (uu___183_10760.defer_ok);
                                      smt_ok = (uu___183_10760.smt_ok);
                                      tcenv = (uu___183_10760.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10762 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10767 -> FStar_Pervasives_Native.None))))
              | uu____10768 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10777 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10777
         then
           let uu____10778 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10778
         else ());
        (let uu____10780 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10780 with
         | (u,args) ->
             let uu____10819 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10819 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10860 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10860 with
                    | (h1,args1) ->
                        let uu____10901 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10901 with
                         | (h2,uu____10921) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10948 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10948
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10966 =
                                          let uu____10969 =
                                            let uu____10970 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_55  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_55) uu____10970 in
                                          [uu____10969] in
                                        FStar_Pervasives_Native.Some
                                          uu____10966))
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
                                       (let uu____11003 =
                                          let uu____11006 =
                                            let uu____11007 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____11007 in
                                          [uu____11006] in
                                        FStar_Pervasives_Native.Some
                                          uu____11003))
                                  else FStar_Pervasives_Native.None
                              | uu____11021 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11111 =
                               let uu____11120 =
                                 let uu____11123 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11123 in
                               (uu____11120, m1) in
                             FStar_Pervasives_Native.Some uu____11111)
                    | (uu____11136,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11138)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11186),uu____11187) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11234 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11287) ->
                       let uu____11312 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___154_11338  ->
                                 match uu___154_11338 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11345 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11345 with
                                           | (u',uu____11361) ->
                                               let uu____11382 =
                                                 let uu____11383 =
                                                   whnf env u' in
                                                 uu____11383.FStar_Syntax_Syntax.n in
                                               (match uu____11382 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11387) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11412 -> false))
                                      | uu____11413 -> false)
                                 | uu____11416 -> false)) in
                       (match uu____11312 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11454 tps =
                              match uu____11454 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11516 =
                                         let uu____11527 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11527 in
                                       (match uu____11516 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11578 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11589 =
                              let uu____11600 =
                                let uu____11609 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11609, []) in
                              make_upper_bound uu____11600 upper_bounds in
                            (match uu____11589 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11623 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11623
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
                                 ((let uu____11649 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11649
                                   then
                                     let wl' =
                                       let uu___184_11651 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___184_11651.wl_deferred);
                                         ctr = (uu___184_11651.ctr);
                                         defer_ok = (uu___184_11651.defer_ok);
                                         smt_ok = (uu___184_11651.smt_ok);
                                         tcenv = (uu___184_11651.tcenv)
                                       } in
                                     let uu____11652 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11652
                                   else ());
                                  (let uu____11654 =
                                     solve_t env eq_prob
                                       (let uu___185_11656 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___185_11656.wl_deferred);
                                          ctr = (uu___185_11656.ctr);
                                          defer_ok =
                                            (uu___185_11656.defer_ok);
                                          smt_ok = (uu___185_11656.smt_ok);
                                          tcenv = (uu___185_11656.tcenv)
                                        }) in
                                   match uu____11654 with
                                   | Success uu____11659 ->
                                       let wl1 =
                                         let uu___186_11661 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___186_11661.wl_deferred);
                                           ctr = (uu___186_11661.ctr);
                                           defer_ok =
                                             (uu___186_11661.defer_ok);
                                           smt_ok = (uu___186_11661.smt_ok);
                                           tcenv = (uu___186_11661.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11663 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11668 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11669 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11760 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11760
                      then
                        let uu____11761 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11761
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___187_11815 = hd1 in
                      let uu____11816 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___187_11815.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___187_11815.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11816
                      } in
                    let hd21 =
                      let uu___188_11820 = hd2 in
                      let uu____11821 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___188_11820.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___188_11820.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11821
                      } in
                    let prob =
                      let uu____11825 =
                        let uu____11830 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11830 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_57  -> FStar_TypeChecker_Common.TProb _0_57)
                        uu____11825 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11841 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11841 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11845 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11845 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11875 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11880 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11875 uu____11880 in
                         ((let uu____11890 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11890
                           then
                             let uu____11891 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11892 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11891 uu____11892
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11915 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11925 = aux scope env [] bs1 bs2 in
              match uu____11925 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11949 = compress_tprob wl problem in
        solve_t' env uu____11949 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11982 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11982 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12013,uu____12014) ->
                   let rec may_relate head3 =
                     let uu____12039 =
                       let uu____12040 = FStar_Syntax_Subst.compress head3 in
                       uu____12040.FStar_Syntax_Syntax.n in
                     match uu____12039 with
                     | FStar_Syntax_Syntax.Tm_name uu____12043 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12044 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12069,uu____12070) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12112) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12118) ->
                         may_relate t
                     | uu____12123 -> false in
                   let uu____12124 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12124
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
                                let uu____12141 =
                                  let uu____12142 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12142 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12141 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12144 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12144
                   else
                     (let uu____12146 =
                        let uu____12147 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12148 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12147 uu____12148 in
                      giveup env1 uu____12146 orig)
               | (uu____12149,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___189_12163 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___189_12163.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___189_12163.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___189_12163.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___189_12163.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___189_12163.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___189_12163.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___189_12163.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___189_12163.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12164,FStar_Pervasives_Native.None ) ->
                   ((let uu____12176 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12176
                     then
                       let uu____12177 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12178 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12179 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12180 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12177
                         uu____12178 uu____12179 uu____12180
                     else ());
                    (let uu____12182 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12182 with
                     | (head11,args1) ->
                         let uu____12219 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12219 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12273 =
                                  let uu____12274 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12275 = args_to_string args1 in
                                  let uu____12276 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12277 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12274 uu____12275 uu____12276
                                    uu____12277 in
                                giveup env1 uu____12273 orig
                              else
                                (let uu____12279 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12285 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12285 = FStar_Syntax_Util.Equal) in
                                 if uu____12279
                                 then
                                   let uu____12286 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12286 with
                                   | USolved wl2 ->
                                       let uu____12288 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12288
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12292 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12292 with
                                    | (base1,refinement1) ->
                                        let uu____12329 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12329 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12410 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12410 with
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
                                                           (fun uu____12432 
                                                              ->
                                                              fun uu____12433
                                                                 ->
                                                                match 
                                                                  (uu____12432,
                                                                    uu____12433)
                                                                with
                                                                | ((a,uu____12451),
                                                                   (a',uu____12453))
                                                                    ->
                                                                    let uu____12462
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
                                                                    _0_58  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_58)
                                                                    uu____12462)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12472 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12472 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12478 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___190_12526 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___190_12526.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12565 =
          match uu____12565 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12781  ->
                              match uu____12781 with
                              | (x,imp) ->
                                  let uu____12792 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12792, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12805 = FStar_Syntax_Util.type_u () in
                      match uu____12805 with
                      | (t1,uu____12811) ->
                          let uu____12812 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12812 in
                    let uu____12817 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12817 with
                     | (t',tm_u1) ->
                         let uu____12830 = destruct_flex_t t' in
                         (match uu____12830 with
                          | (uu____12867,u1,k1,uu____12870) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12929 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12929 in
                              let sol =
                                let uu____12933 =
                                  let uu____12942 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12942) in
                                TERM uu____12933 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13078 = pat_var_opt env pat_args hd1 in
                    (match uu____13078 with
                     | FStar_Pervasives_Native.None  ->
                         aux pat_args pattern_vars pattern_var_set (formal ::
                           seen_formals) formals1 res_t tl1
                     | FStar_Pervasives_Native.Some y ->
                         let maybe_pat =
                           match xs_opt with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some xs ->
                               FStar_All.pipe_right xs
                                 (FStar_Util.for_some
                                    (fun uu____13141  ->
                                       match uu____13141 with
                                       | (x,uu____13147) ->
                                           FStar_Syntax_Syntax.bv_eq x
                                             (FStar_Pervasives_Native.fst y))) in
                         if Prims.op_Negation maybe_pat
                         then
                           aux pat_args pattern_vars pattern_var_set (formal
                             :: seen_formals) formals1 res_t tl1
                         else
                           (let fvs =
                              FStar_Syntax_Free.names
                                (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                            let uu____13162 =
                              let uu____13163 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____13163 in
                            if uu____13162
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____13175 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____13175 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____13190::uu____13191) ->
                    let uu____13222 =
                      let uu____13235 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13235 in
                    (match uu____13222 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13274 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13281::uu____13282,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13317 =
                let uu____13330 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13330 in
              (match uu____13317 with
               | (all_formals,res_t) ->
                   let uu____13355 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13355 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13389 = lhs in
          match uu____13389 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13399 ->
                    let uu____13400 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13400 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13429 = p in
          match uu____13429 with
          | (((u,k),xs,c),ps,(h,uu____13440,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13522 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13522 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13545 = h gs_xs in
                     let uu____13546 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59) in
                     FStar_Syntax_Util.abs xs1 uu____13545 uu____13546 in
                   ((let uu____13552 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13552
                     then
                       let uu____13553 =
                         let uu____13556 =
                           let uu____13557 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13557
                             (FStar_String.concat "\n\t") in
                         let uu____13562 =
                           let uu____13565 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13566 =
                             let uu____13569 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13570 =
                               let uu____13573 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13574 =
                                 let uu____13577 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13578 =
                                   let uu____13581 =
                                     let uu____13582 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13582
                                       (FStar_String.concat ", ") in
                                   let uu____13587 =
                                     let uu____13590 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13590] in
                                   uu____13581 :: uu____13587 in
                                 uu____13577 :: uu____13578 in
                               uu____13573 :: uu____13574 in
                             uu____13569 :: uu____13570 in
                           uu____13565 :: uu____13566 in
                         uu____13556 :: uu____13562 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13553
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___155_13611 =
          match uu___155_13611 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13643 = p in
          match uu____13643 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13734 = FStar_List.nth ps i in
              (match uu____13734 with
               | (pi,uu____13738) ->
                   let uu____13743 = FStar_List.nth xs i in
                   (match uu____13743 with
                    | (xi,uu____13755) ->
                        let rec gs k =
                          let uu____13768 =
                            let uu____13781 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13781 in
                          match uu____13768 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13856)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13869 = new_uvar r xs k_a in
                                    (match uu____13869 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs in
                                         let gi_ps =
                                           FStar_Syntax_Syntax.mk_Tm_app gi
                                             ps FStar_Pervasives_Native.None
                                             r in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1 in
                                         let uu____13891 = aux subst2 tl1 in
                                         (match uu____13891 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13918 =
                                                let uu____13921 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13921 :: gi_xs' in
                                              let uu____13922 =
                                                let uu____13925 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13925 :: gi_ps' in
                                              (uu____13918, uu____13922))) in
                              aux [] bs in
                        let uu____13930 =
                          let uu____13931 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13931 in
                        if uu____13930
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13935 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13935 with
                           | (g_xs,uu____13947) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13958 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13959 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_60  ->
                                        FStar_Pervasives_Native.Some _0_60) in
                                 FStar_Syntax_Util.abs xs uu____13958
                                   uu____13959 in
                               let sub1 =
                                 let uu____13965 =
                                   let uu____13970 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13973 =
                                     let uu____13976 =
                                       FStar_List.map
                                         (fun uu____13991  ->
                                            match uu____13991 with
                                            | (uu____14000,uu____14001,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13976 in
                                   mk_problem (p_scope orig) orig uu____13970
                                     (p_rel orig) uu____13973
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____13965 in
                               ((let uu____14016 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14016
                                 then
                                   let uu____14017 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____14018 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14017 uu____14018
                                 else ());
                                (let wl2 =
                                   let uu____14021 =
                                     let uu____14024 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____14024 in
                                   solve_prob orig uu____14021
                                     [TERM (u, proj)] wl1 in
                                 let uu____14033 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____14033))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14064 = lhs in
          match uu____14064 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14100 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14100 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14133 =
                        let uu____14180 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14180) in
                      FStar_Pervasives_Native.Some uu____14133
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14324 =
                           let uu____14331 =
                             let uu____14332 = FStar_Syntax_Subst.compress k1 in
                             uu____14332.FStar_Syntax_Syntax.n in
                           (uu____14331, args) in
                         match uu____14324 with
                         | (uu____14343,[]) ->
                             let uu____14346 =
                               let uu____14357 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14357) in
                             FStar_Pervasives_Native.Some uu____14346
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14378,uu____14379) ->
                             let uu____14400 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14400 with
                              | (uv1,uv_args) ->
                                  let uu____14443 =
                                    let uu____14444 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14444.FStar_Syntax_Syntax.n in
                                  (match uu____14443 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14454) ->
                                       let uu____14479 =
                                         pat_vars env [] uv_args in
                                       (match uu____14479 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14506  ->
                                                      let uu____14507 =
                                                        let uu____14508 =
                                                          let uu____14509 =
                                                            let uu____14514 =
                                                              let uu____14515
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14515
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14514 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14509 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14508 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14507)) in
                                            let c1 =
                                              let uu____14525 =
                                                let uu____14526 =
                                                  let uu____14531 =
                                                    let uu____14532 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14532
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14531 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14526 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14525 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14545 =
                                                let uu____14548 =
                                                  let uu____14549 =
                                                    let uu____14552 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14552
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14549 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14548 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14545 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14570 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14575,uu____14576) ->
                             let uu____14595 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14595 with
                              | (uv1,uv_args) ->
                                  let uu____14638 =
                                    let uu____14639 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14639.FStar_Syntax_Syntax.n in
                                  (match uu____14638 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14649) ->
                                       let uu____14674 =
                                         pat_vars env [] uv_args in
                                       (match uu____14674 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14701  ->
                                                      let uu____14702 =
                                                        let uu____14703 =
                                                          let uu____14704 =
                                                            let uu____14709 =
                                                              let uu____14710
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14710
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14709 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14704 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14703 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14702)) in
                                            let c1 =
                                              let uu____14720 =
                                                let uu____14721 =
                                                  let uu____14726 =
                                                    let uu____14727 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14727
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14726 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14721 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14720 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14740 =
                                                let uu____14743 =
                                                  let uu____14744 =
                                                    let uu____14747 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14747
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14744 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14743 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14740 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14765 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14772) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14813 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14813
                                 (fun _0_63  ->
                                    FStar_Pervasives_Native.Some _0_63)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14849 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14849 with
                                  | (args1,rest) ->
                                      let uu____14878 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14878 with
                                       | (xs2,c2) ->
                                           let uu____14891 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14891
                                             (fun uu____14915  ->
                                                match uu____14915 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14955 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14955 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____15023 =
                                        let uu____15028 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15028 in
                                      FStar_All.pipe_right uu____15023
                                        (fun _0_64  ->
                                           FStar_Pervasives_Native.Some _0_64))
                         | uu____15043 ->
                             let uu____15050 =
                               let uu____15051 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____15052 =
                                 FStar_Syntax_Print.term_to_string k1 in
                               let uu____15053 =
                                 FStar_Syntax_Print.term_to_string k_uv in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____15051 uu____15052 uu____15053 in
                             failwith uu____15050 in
                       let uu____15060 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15060
                         (fun uu____15115  ->
                            match uu____15115 with
                            | (xs1,c1) ->
                                let uu____15164 =
                                  let uu____15205 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15205) in
                                FStar_Pervasives_Native.Some uu____15164)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15326 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15342 = project orig env wl1 i st in
                     match uu____15342 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15356) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15371 = imitate orig env wl1 st in
                  match uu____15371 with
                  | Failed uu____15376 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15407 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15407 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15432 =
                      let uu____15433 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15433 wl2 in
                    (match uu____15432 with
                     | Failed uu____15434 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15452 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15452 with
                | (hd1,uu____15468) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15489 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15502 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15503 -> true
                     | uu____15520 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15524 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15524
                         then true
                         else
                           ((let uu____15527 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15527
                             then
                               let uu____15528 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____15528
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15548 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15548 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15561 =
                            let uu____15562 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15562 in
                          giveup_or_defer1 orig uu____15561
                        else
                          (let uu____15564 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15564
                           then
                             let uu____15565 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15565
                              then
                                let uu____15566 = subterms args_lhs in
                                imitate' orig env wl1 uu____15566
                              else
                                ((let uu____15571 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15571
                                  then
                                    let uu____15572 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15573 = names_to_string fvs1 in
                                    let uu____15574 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15572 uu____15573 uu____15574
                                  else ());
                                 use_pattern_equality orig env wl1 lhs1 vars
                                   t21))
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
                               (let uu____15578 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15578
                                then
                                  ((let uu____15580 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15580
                                    then
                                      let uu____15581 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15582 = names_to_string fvs1 in
                                      let uu____15583 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15581 uu____15582 uu____15583
                                    else ());
                                   (let uu____15585 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15585))
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
                     (let uu____15596 =
                        let uu____15597 = FStar_Syntax_Free.names t1 in
                        check_head uu____15597 t2 in
                      if uu____15596
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15608 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15608
                          then
                            let uu____15609 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15610 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15609 uu____15610
                          else ());
                         (let uu____15618 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15618))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15695 uu____15696 r =
               match (uu____15695, uu____15696) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15894 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15894
                   then
                     let uu____15895 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15895
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15919 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15919
                       then
                         let uu____15920 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15921 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15922 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15923 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15924 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15920 uu____15921 uu____15922 uu____15923
                           uu____15924
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15984 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15984 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15998 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15998 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16052 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16052 in
                                  let uu____16055 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16055 k3)
                           else
                             (let uu____16059 =
                                let uu____16060 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16061 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16062 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16060 uu____16061 uu____16062 in
                              failwith uu____16059) in
                       let uu____16063 =
                         let uu____16072 =
                           let uu____16085 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16085 in
                         match uu____16072 with
                         | (bs,k1') ->
                             let uu____16112 =
                               let uu____16125 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16125 in
                             (match uu____16112 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16155 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      uu____16155 in
                                  let uu____16164 =
                                    let uu____16169 =
                                      let uu____16170 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16170.FStar_Syntax_Syntax.n in
                                    let uu____16173 =
                                      let uu____16174 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16174.FStar_Syntax_Syntax.n in
                                    (uu____16169, uu____16173) in
                                  (match uu____16164 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16185,uu____16186) ->
                                       (k1', [sub_prob])
                                   | (uu____16191,FStar_Syntax_Syntax.Tm_type
                                      uu____16192) -> (k2', [sub_prob])
                                   | uu____16197 ->
                                       let uu____16202 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16202 with
                                        | (t,uu____16216) ->
                                            let uu____16217 = new_uvar r zs t in
                                            (match uu____16217 with
                                             | (k_zs,uu____16231) ->
                                                 let kprob =
                                                   let uu____16233 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_66  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_66) uu____16233 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16063 with
                       | (k_u',sub_probs) ->
                           let uu____16254 =
                             let uu____16265 =
                               let uu____16266 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16266 in
                             let uu____16275 =
                               let uu____16278 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16278 in
                             let uu____16281 =
                               let uu____16284 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16284 in
                             (uu____16265, uu____16275, uu____16281) in
                           (match uu____16254 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16303 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16303 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16322 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16322
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16326 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16326 with
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
             let solve_one_pat uu____16379 uu____16380 =
               match (uu____16379, uu____16380) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16498 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16498
                     then
                       let uu____16499 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16500 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16499 uu____16500
                     else ());
                    (let uu____16502 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16502
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16521  ->
                              fun uu____16522  ->
                                match (uu____16521, uu____16522) with
                                | ((a,uu____16540),(t21,uu____16542)) ->
                                    let uu____16551 =
                                      let uu____16556 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16556
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16551
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67))
                           xs args2 in
                       let guard =
                         let uu____16562 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16562 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16577 = occurs_check env wl (u1, k1) t21 in
                        match uu____16577 with
                        | (occurs_ok,uu____16585) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16593 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16593
                            then
                              let sol =
                                let uu____16595 =
                                  let uu____16604 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16604) in
                                TERM uu____16595 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16611 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16611
                               then
                                 let uu____16612 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16612 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16636,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16662 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16662
                                       then
                                         let uu____16663 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16663
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16670 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16672 = lhs in
             match uu____16672 with
             | (t1,u1,k1,args1) ->
                 let uu____16677 = rhs in
                 (match uu____16677 with
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
                       | uu____16717 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16727 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16727 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16745) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16752 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16752
                                    then
                                      let uu____16753 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16753
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16760 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16762 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16762
        then
          let uu____16763 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16763
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16767 = FStar_Util.physical_equality t1 t2 in
           if uu____16767
           then
             let uu____16768 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16768
           else
             ((let uu____16771 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16771
               then
                 let uu____16772 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16772
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16775,uu____16776) ->
                   let uu____16803 =
                     let uu___191_16804 = problem in
                     let uu____16805 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___191_16804.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16805;
                       FStar_TypeChecker_Common.relation =
                         (uu___191_16804.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___191_16804.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___191_16804.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___191_16804.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___191_16804.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___191_16804.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___191_16804.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___191_16804.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16803 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16806,uu____16807) ->
                   let uu____16814 =
                     let uu___191_16815 = problem in
                     let uu____16816 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___191_16815.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16816;
                       FStar_TypeChecker_Common.relation =
                         (uu___191_16815.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___191_16815.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___191_16815.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___191_16815.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___191_16815.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___191_16815.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___191_16815.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___191_16815.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16814 wl
               | (uu____16817,FStar_Syntax_Syntax.Tm_ascribed uu____16818) ->
                   let uu____16845 =
                     let uu___192_16846 = problem in
                     let uu____16847 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___192_16846.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___192_16846.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___192_16846.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16847;
                       FStar_TypeChecker_Common.element =
                         (uu___192_16846.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___192_16846.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___192_16846.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___192_16846.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___192_16846.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___192_16846.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16845 wl
               | (uu____16848,FStar_Syntax_Syntax.Tm_meta uu____16849) ->
                   let uu____16856 =
                     let uu___192_16857 = problem in
                     let uu____16858 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___192_16857.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___192_16857.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___192_16857.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16858;
                       FStar_TypeChecker_Common.element =
                         (uu___192_16857.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___192_16857.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___192_16857.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___192_16857.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___192_16857.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___192_16857.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16856 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16859,uu____16860) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16861,FStar_Syntax_Syntax.Tm_bvar uu____16862) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___156_16917 =
                     match uu___156_16917 with
                     | [] -> c
                     | bs ->
                         let uu____16939 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16939 in
                   let uu____16948 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16948 with
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
                                   let uu____17090 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17090
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17092 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.CProb _0_68)
                                   uu____17092))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___157_17168 =
                     match uu___157_17168 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17202 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17202 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17338 =
                                   let uu____17343 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17344 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17343
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17344 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17338))
               | (FStar_Syntax_Syntax.Tm_abs uu____17349,uu____17350) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17375 -> true
                     | uu____17392 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17426 =
                     let uu____17443 = maybe_eta t1 in
                     let uu____17450 = maybe_eta t2 in
                     (uu____17443, uu____17450) in
                   (match uu____17426 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___193_17492 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___193_17492.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___193_17492.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___193_17492.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___193_17492.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___193_17492.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___193_17492.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___193_17492.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___193_17492.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17515 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17515
                        then
                          let uu____17516 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17516 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17544 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17544
                        then
                          let uu____17545 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17545 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17553 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17570,FStar_Syntax_Syntax.Tm_abs uu____17571) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17596 -> true
                     | uu____17613 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17647 =
                     let uu____17664 = maybe_eta t1 in
                     let uu____17671 = maybe_eta t2 in
                     (uu____17664, uu____17671) in
                   (match uu____17647 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___193_17713 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___193_17713.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___193_17713.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___193_17713.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___193_17713.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___193_17713.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___193_17713.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___193_17713.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___193_17713.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17736 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17736
                        then
                          let uu____17737 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17737 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17765 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17765
                        then
                          let uu____17766 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17766 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17774 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17791,FStar_Syntax_Syntax.Tm_refine uu____17792) ->
                   let uu____17805 = as_refinement env wl t1 in
                   (match uu____17805 with
                    | (x1,phi1) ->
                        let uu____17812 = as_refinement env wl t2 in
                        (match uu____17812 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17820 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_70  ->
                                    FStar_TypeChecker_Common.TProb _0_70)
                                 uu____17820 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17858 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17858
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17862 =
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
                                 let uu____17868 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17868 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17877 =
                                   let uu____17882 =
                                     let uu____17883 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____17883 :: (p_scope orig) in
                                   mk_problem uu____17882 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.TProb _0_71)
                                   uu____17877 in
                               let uu____17888 =
                                 solve env1
                                   (let uu___194_17890 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___194_17890.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___194_17890.smt_ok);
                                      tcenv = (uu___194_17890.tcenv)
                                    }) in
                               (match uu____17888 with
                                | Failed uu____17897 -> fallback ()
                                | Success uu____17902 ->
                                    let guard =
                                      let uu____17906 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17911 =
                                        let uu____17912 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17912
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17906
                                        uu____17911 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___195_17921 = wl1 in
                                      {
                                        attempting =
                                          (uu___195_17921.attempting);
                                        wl_deferred =
                                          (uu___195_17921.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___195_17921.defer_ok);
                                        smt_ok = (uu___195_17921.smt_ok);
                                        tcenv = (uu___195_17921.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17923,FStar_Syntax_Syntax.Tm_uvar uu____17924) ->
                   let uu____17957 = destruct_flex_t t1 in
                   let uu____17958 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17957 uu____17958
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17959;
                     FStar_Syntax_Syntax.pos = uu____17960;
                     FStar_Syntax_Syntax.vars = uu____17961;_},uu____17962),FStar_Syntax_Syntax.Tm_uvar
                  uu____17963) ->
                   let uu____18016 = destruct_flex_t t1 in
                   let uu____18017 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18016 uu____18017
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18018,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18019;
                     FStar_Syntax_Syntax.pos = uu____18020;
                     FStar_Syntax_Syntax.vars = uu____18021;_},uu____18022))
                   ->
                   let uu____18075 = destruct_flex_t t1 in
                   let uu____18076 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18075 uu____18076
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18077;
                     FStar_Syntax_Syntax.pos = uu____18078;
                     FStar_Syntax_Syntax.vars = uu____18079;_},uu____18080),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18081;
                     FStar_Syntax_Syntax.pos = uu____18082;
                     FStar_Syntax_Syntax.vars = uu____18083;_},uu____18084))
                   ->
                   let uu____18157 = destruct_flex_t t1 in
                   let uu____18158 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18157 uu____18158
               | (FStar_Syntax_Syntax.Tm_uvar uu____18159,uu____18160) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18177 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18177 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18184;
                     FStar_Syntax_Syntax.pos = uu____18185;
                     FStar_Syntax_Syntax.vars = uu____18186;_},uu____18187),uu____18188)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18225 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18225 t2 wl
               | (uu____18232,FStar_Syntax_Syntax.Tm_uvar uu____18233) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18250,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18251;
                     FStar_Syntax_Syntax.pos = uu____18252;
                     FStar_Syntax_Syntax.vars = uu____18253;_},uu____18254))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18291,FStar_Syntax_Syntax.Tm_type uu____18292) ->
                   solve_t' env
                     (let uu___196_18310 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___196_18310.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___196_18310.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___196_18310.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___196_18310.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___196_18310.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___196_18310.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___196_18310.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___196_18310.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___196_18310.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18311;
                     FStar_Syntax_Syntax.pos = uu____18312;
                     FStar_Syntax_Syntax.vars = uu____18313;_},uu____18314),FStar_Syntax_Syntax.Tm_type
                  uu____18315) ->
                   solve_t' env
                     (let uu___196_18353 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___196_18353.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___196_18353.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___196_18353.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___196_18353.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___196_18353.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___196_18353.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___196_18353.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___196_18353.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___196_18353.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18354,FStar_Syntax_Syntax.Tm_arrow uu____18355) ->
                   solve_t' env
                     (let uu___196_18385 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___196_18385.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___196_18385.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___196_18385.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___196_18385.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___196_18385.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___196_18385.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___196_18385.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___196_18385.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___196_18385.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18386;
                     FStar_Syntax_Syntax.pos = uu____18387;
                     FStar_Syntax_Syntax.vars = uu____18388;_},uu____18389),FStar_Syntax_Syntax.Tm_arrow
                  uu____18390) ->
                   solve_t' env
                     (let uu___196_18440 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___196_18440.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___196_18440.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___196_18440.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___196_18440.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___196_18440.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___196_18440.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___196_18440.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___196_18440.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___196_18440.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18441,uu____18442) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18461 =
                        let uu____18462 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18462 in
                      if uu____18461
                      then
                        let uu____18463 =
                          FStar_All.pipe_left
                            (fun _0_72  ->
                               FStar_TypeChecker_Common.TProb _0_72)
                            (let uu___197_18469 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___197_18469.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___197_18469.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___197_18469.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___197_18469.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___197_18469.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___197_18469.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___197_18469.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___197_18469.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___197_18469.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18470 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18463 uu____18470 t2
                          wl
                      else
                        (let uu____18478 = base_and_refinement env wl t2 in
                         match uu____18478 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18521 =
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      (let uu___198_18527 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___198_18527.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___198_18527.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___198_18527.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___198_18527.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___198_18527.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___198_18527.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___198_18527.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___198_18527.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___198_18527.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18528 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18521
                                    uu____18528 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___199_18548 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___199_18548.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___199_18548.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18551 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      uu____18551 in
                                  let guard =
                                    let uu____18563 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18563
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18571;
                     FStar_Syntax_Syntax.pos = uu____18572;
                     FStar_Syntax_Syntax.vars = uu____18573;_},uu____18574),uu____18575)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18614 =
                        let uu____18615 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18615 in
                      if uu____18614
                      then
                        let uu____18616 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___197_18622 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___197_18622.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___197_18622.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___197_18622.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___197_18622.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___197_18622.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___197_18622.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___197_18622.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___197_18622.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___197_18622.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18623 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18616 uu____18623 t2
                          wl
                      else
                        (let uu____18631 = base_and_refinement env wl t2 in
                         match uu____18631 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18674 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___198_18680 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___198_18680.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___198_18680.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___198_18680.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___198_18680.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___198_18680.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___198_18680.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___198_18680.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___198_18680.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___198_18680.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18681 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18674
                                    uu____18681 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___199_18701 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___199_18701.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___199_18701.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18704 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____18704 in
                                  let guard =
                                    let uu____18716 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18716
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18724,FStar_Syntax_Syntax.Tm_uvar uu____18725) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18743 = base_and_refinement env wl t1 in
                      match uu____18743 with
                      | (t_base,uu____18759) ->
                          solve_t env
                            (let uu___200_18781 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___200_18781.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___200_18781.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___200_18781.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___200_18781.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___200_18781.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___200_18781.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___200_18781.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___200_18781.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18784,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18785;
                     FStar_Syntax_Syntax.pos = uu____18786;
                     FStar_Syntax_Syntax.vars = uu____18787;_},uu____18788))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18826 = base_and_refinement env wl t1 in
                      match uu____18826 with
                      | (t_base,uu____18842) ->
                          solve_t env
                            (let uu___200_18864 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___200_18864.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___200_18864.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___200_18864.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___200_18864.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___200_18864.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___200_18864.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___200_18864.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___200_18864.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18867,uu____18868) ->
                   let t21 =
                     let uu____18878 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18878 in
                   solve_t env
                     (let uu___201_18902 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___201_18902.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___201_18902.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___201_18902.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___201_18902.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___201_18902.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___201_18902.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___201_18902.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___201_18902.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___201_18902.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18903,FStar_Syntax_Syntax.Tm_refine uu____18904) ->
                   let t11 =
                     let uu____18914 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18914 in
                   solve_t env
                     (let uu___202_18938 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___202_18938.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___202_18938.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___202_18938.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___202_18938.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___202_18938.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___202_18938.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___202_18938.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___202_18938.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___202_18938.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18941,uu____18942) ->
                   let head1 =
                     let uu____18968 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18968
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19012 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19012
                       FStar_Pervasives_Native.fst in
                   let uu____19053 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19053
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19068 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19068
                      then
                        let guard =
                          let uu____19080 =
                            let uu____19081 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19081 = FStar_Syntax_Util.Equal in
                          if uu____19080
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19085 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19085) in
                        let uu____19088 = solve_prob orig guard [] wl in
                        solve env uu____19088
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19091,uu____19092) ->
                   let head1 =
                     let uu____19102 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19102
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19146 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19146
                       FStar_Pervasives_Native.fst in
                   let uu____19187 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19187
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19202 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19202
                      then
                        let guard =
                          let uu____19214 =
                            let uu____19215 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19215 = FStar_Syntax_Util.Equal in
                          if uu____19214
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19219 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19219) in
                        let uu____19222 = solve_prob orig guard [] wl in
                        solve env uu____19222
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19225,uu____19226) ->
                   let head1 =
                     let uu____19230 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19230
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19274 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19274
                       FStar_Pervasives_Native.fst in
                   let uu____19315 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19315
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19330 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19330
                      then
                        let guard =
                          let uu____19342 =
                            let uu____19343 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19343 = FStar_Syntax_Util.Equal in
                          if uu____19342
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19347 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19347) in
                        let uu____19350 = solve_prob orig guard [] wl in
                        solve env uu____19350
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19353,uu____19354) ->
                   let head1 =
                     let uu____19358 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19358
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19402 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19402
                       FStar_Pervasives_Native.fst in
                   let uu____19443 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19443
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19458 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19458
                      then
                        let guard =
                          let uu____19470 =
                            let uu____19471 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19471 = FStar_Syntax_Util.Equal in
                          if uu____19470
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19475 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19475) in
                        let uu____19478 = solve_prob orig guard [] wl in
                        solve env uu____19478
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19481,uu____19482) ->
                   let head1 =
                     let uu____19486 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19486
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19530 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19530
                       FStar_Pervasives_Native.fst in
                   let uu____19571 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19571
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19586 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19586
                      then
                        let guard =
                          let uu____19598 =
                            let uu____19599 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19599 = FStar_Syntax_Util.Equal in
                          if uu____19598
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19603 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19603) in
                        let uu____19606 = solve_prob orig guard [] wl in
                        solve env uu____19606
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19609,uu____19610) ->
                   let head1 =
                     let uu____19628 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19628
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19672 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19672
                       FStar_Pervasives_Native.fst in
                   let uu____19713 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19713
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19728 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19728
                      then
                        let guard =
                          let uu____19740 =
                            let uu____19741 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19741 = FStar_Syntax_Util.Equal in
                          if uu____19740
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19745 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19745) in
                        let uu____19748 = solve_prob orig guard [] wl in
                        solve env uu____19748
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19751,FStar_Syntax_Syntax.Tm_match uu____19752) ->
                   let head1 =
                     let uu____19778 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19778
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19822 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19822
                       FStar_Pervasives_Native.fst in
                   let uu____19863 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19863
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19878 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19878
                      then
                        let guard =
                          let uu____19890 =
                            let uu____19891 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19891 = FStar_Syntax_Util.Equal in
                          if uu____19890
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19895 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19895) in
                        let uu____19898 = solve_prob orig guard [] wl in
                        solve env uu____19898
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19901,FStar_Syntax_Syntax.Tm_uinst uu____19902) ->
                   let head1 =
                     let uu____19912 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19912
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19956 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19956
                       FStar_Pervasives_Native.fst in
                   let uu____19997 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19997
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20012 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20012
                      then
                        let guard =
                          let uu____20024 =
                            let uu____20025 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20025 = FStar_Syntax_Util.Equal in
                          if uu____20024
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20029 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20029) in
                        let uu____20032 = solve_prob orig guard [] wl in
                        solve env uu____20032
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20035,FStar_Syntax_Syntax.Tm_name uu____20036) ->
                   let head1 =
                     let uu____20040 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20040
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20084 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20084
                       FStar_Pervasives_Native.fst in
                   let uu____20125 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20125
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20140 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20140
                      then
                        let guard =
                          let uu____20152 =
                            let uu____20153 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20153 = FStar_Syntax_Util.Equal in
                          if uu____20152
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20157 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20157) in
                        let uu____20160 = solve_prob orig guard [] wl in
                        solve env uu____20160
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20163,FStar_Syntax_Syntax.Tm_constant uu____20164) ->
                   let head1 =
                     let uu____20168 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20168
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20212 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20212
                       FStar_Pervasives_Native.fst in
                   let uu____20253 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20253
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20268 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20268
                      then
                        let guard =
                          let uu____20280 =
                            let uu____20281 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20281 = FStar_Syntax_Util.Equal in
                          if uu____20280
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20285 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20285) in
                        let uu____20288 = solve_prob orig guard [] wl in
                        solve env uu____20288
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20291,FStar_Syntax_Syntax.Tm_fvar uu____20292) ->
                   let head1 =
                     let uu____20296 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20296
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20340 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20340
                       FStar_Pervasives_Native.fst in
                   let uu____20381 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20381
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20396 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20396
                      then
                        let guard =
                          let uu____20408 =
                            let uu____20409 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20409 = FStar_Syntax_Util.Equal in
                          if uu____20408
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20413 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20413) in
                        let uu____20416 = solve_prob orig guard [] wl in
                        solve env uu____20416
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20419,FStar_Syntax_Syntax.Tm_app uu____20420) ->
                   let head1 =
                     let uu____20438 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20438
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20482 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20482
                       FStar_Pervasives_Native.fst in
                   let uu____20523 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20523
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20538 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20538
                      then
                        let guard =
                          let uu____20550 =
                            let uu____20551 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20551 = FStar_Syntax_Util.Equal in
                          if uu____20550
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20555 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_Pervasives_Native.Some _0_89)
                               uu____20555) in
                        let uu____20558 = solve_prob orig guard [] wl in
                        solve env uu____20558
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20561,uu____20562) ->
                   let uu____20575 =
                     let uu____20576 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20577 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20576
                       uu____20577 in
                   failwith uu____20575
               | (FStar_Syntax_Syntax.Tm_delayed uu____20578,uu____20579) ->
                   let uu____20604 =
                     let uu____20605 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20606 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20605
                       uu____20606 in
                   failwith uu____20604
               | (uu____20607,FStar_Syntax_Syntax.Tm_delayed uu____20608) ->
                   let uu____20633 =
                     let uu____20634 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20635 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20634
                       uu____20635 in
                   failwith uu____20633
               | (uu____20636,FStar_Syntax_Syntax.Tm_let uu____20637) ->
                   let uu____20650 =
                     let uu____20651 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20652 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20651
                       uu____20652 in
                   failwith uu____20650
               | uu____20653 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20689 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20689
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20691 =
               let uu____20692 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20693 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20692 uu____20693 in
             giveup env uu____20691 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20713  ->
                    fun uu____20714  ->
                      match (uu____20713, uu____20714) with
                      | ((a1,uu____20732),(a2,uu____20734)) ->
                          let uu____20743 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_90  ->
                               FStar_TypeChecker_Common.TProb _0_90)
                            uu____20743)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20753 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20753 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20777 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20784)::[] -> wp1
              | uu____20801 ->
                  let uu____20810 =
                    let uu____20811 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20811 in
                  failwith uu____20810 in
            let uu____20814 =
              let uu____20823 =
                let uu____20824 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20824 in
              [uu____20823] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20814;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20825 = lift_c1 () in solve_eq uu____20825 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___158_20831  ->
                       match uu___158_20831 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20832 -> false)) in
             let uu____20833 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20867)::uu____20868,(wp2,uu____20870)::uu____20871)
                   -> (wp1, wp2)
               | uu____20928 ->
                   let uu____20949 =
                     let uu____20950 =
                       let uu____20955 =
                         let uu____20956 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20957 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20956 uu____20957 in
                       (uu____20955, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20950 in
                   FStar_Exn.raise uu____20949 in
             match uu____20833 with
             | (wpc1,wpc2) ->
                 let uu____20976 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20976
                 then
                   let uu____20979 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20979 wl
                 else
                   (let uu____20983 =
                      let uu____20990 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20990 in
                    match uu____20983 with
                    | (c2_decl,qualifiers) ->
                        let uu____21011 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21011
                        then
                          let c1_repr =
                            let uu____21015 =
                              let uu____21016 =
                                let uu____21017 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21017 in
                              let uu____21018 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21016 uu____21018 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____21015 in
                          let c2_repr =
                            let uu____21020 =
                              let uu____21021 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21022 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21021 uu____21022 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____21020 in
                          let prob =
                            let uu____21024 =
                              let uu____21029 =
                                let uu____21030 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21031 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21030
                                  uu____21031 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21029 in
                            FStar_TypeChecker_Common.TProb uu____21024 in
                          let wl1 =
                            let uu____21033 =
                              let uu____21036 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21036 in
                            solve_prob orig uu____21033 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21045 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21045
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____21047 =
                                     let uu____21050 =
                                       let uu____21051 =
                                         let uu____21066 =
                                           let uu____21067 =
                                             let uu____21068 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____21068] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____21067 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21069 =
                                           let uu____21072 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21073 =
                                             let uu____21076 =
                                               let uu____21077 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21077 in
                                             [uu____21076] in
                                           uu____21072 :: uu____21073 in
                                         (uu____21066, uu____21069) in
                                       FStar_Syntax_Syntax.Tm_app uu____21051 in
                                     FStar_Syntax_Syntax.mk uu____21050 in
                                   uu____21047 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____21084 =
                                    let uu____21087 =
                                      let uu____21088 =
                                        let uu____21103 =
                                          let uu____21104 =
                                            let uu____21105 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____21105] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____21104 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21106 =
                                          let uu____21109 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21110 =
                                            let uu____21113 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21114 =
                                              let uu____21117 =
                                                let uu____21118 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21118 in
                                              [uu____21117] in
                                            uu____21113 :: uu____21114 in
                                          uu____21109 :: uu____21110 in
                                        (uu____21103, uu____21106) in
                                      FStar_Syntax_Syntax.Tm_app uu____21088 in
                                    FStar_Syntax_Syntax.mk uu____21087 in
                                  uu____21084 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21125 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_91  ->
                                  FStar_TypeChecker_Common.TProb _0_91)
                               uu____21125 in
                           let wl1 =
                             let uu____21135 =
                               let uu____21138 =
                                 let uu____21141 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21141 g in
                               FStar_All.pipe_left
                                 (fun _0_92  ->
                                    FStar_Pervasives_Native.Some _0_92)
                                 uu____21138 in
                             solve_prob orig uu____21135 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21154 = FStar_Util.physical_equality c1 c2 in
        if uu____21154
        then
          let uu____21155 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21155
        else
          ((let uu____21158 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21158
            then
              let uu____21159 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21160 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21159
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21160
            else ());
           (let uu____21162 =
              let uu____21167 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21168 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21167, uu____21168) in
            match uu____21162 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21172),FStar_Syntax_Syntax.Total
                    (t2,uu____21174)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21191 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21191 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21194,FStar_Syntax_Syntax.Total uu____21195) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21213),FStar_Syntax_Syntax.Total
                    (t2,uu____21215)) ->
                     let uu____21232 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21232 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21236),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21238)) ->
                     let uu____21255 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21255 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21259),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21261)) ->
                     let uu____21278 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21278 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21281,FStar_Syntax_Syntax.Comp uu____21282) ->
                     let uu____21291 =
                       let uu___203_21296 = problem in
                       let uu____21301 =
                         let uu____21302 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21302 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___203_21296.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21301;
                         FStar_TypeChecker_Common.relation =
                           (uu___203_21296.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___203_21296.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___203_21296.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___203_21296.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___203_21296.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___203_21296.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___203_21296.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___203_21296.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21291 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21303,FStar_Syntax_Syntax.Comp uu____21304) ->
                     let uu____21313 =
                       let uu___203_21318 = problem in
                       let uu____21323 =
                         let uu____21324 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21324 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___203_21318.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21323;
                         FStar_TypeChecker_Common.relation =
                           (uu___203_21318.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___203_21318.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___203_21318.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___203_21318.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___203_21318.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___203_21318.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___203_21318.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___203_21318.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21313 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21325,FStar_Syntax_Syntax.GTotal uu____21326) ->
                     let uu____21335 =
                       let uu___204_21340 = problem in
                       let uu____21345 =
                         let uu____21346 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21346 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___204_21340.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___204_21340.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___204_21340.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21345;
                         FStar_TypeChecker_Common.element =
                           (uu___204_21340.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___204_21340.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___204_21340.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___204_21340.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___204_21340.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___204_21340.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21335 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21347,FStar_Syntax_Syntax.Total uu____21348) ->
                     let uu____21357 =
                       let uu___204_21362 = problem in
                       let uu____21367 =
                         let uu____21368 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21368 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___204_21362.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___204_21362.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___204_21362.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21367;
                         FStar_TypeChecker_Common.element =
                           (uu___204_21362.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___204_21362.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___204_21362.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___204_21362.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___204_21362.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___204_21362.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21357 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21369,FStar_Syntax_Syntax.Comp uu____21370) ->
                     let uu____21371 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB)) in
                     if uu____21371
                     then
                       let uu____21372 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21372 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21378 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21388 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21389 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21388, uu____21389)) in
                          match uu____21378 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21396 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21396
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21398 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21398 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21401 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21403 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21403) in
                                if uu____21401
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
                                  (let uu____21406 =
                                     let uu____21407 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21408 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21407 uu____21408 in
                                   giveup env uu____21406 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21414 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21452  ->
              match uu____21452 with
              | (uu____21465,uu____21466,u,uu____21468,uu____21469,uu____21470)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21414 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21502 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21502 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21520 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21548  ->
                match uu____21548 with
                | (u1,u2) ->
                    let uu____21555 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21556 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21555 uu____21556)) in
      FStar_All.pipe_right uu____21520 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21575,[])) -> "{}"
      | uu____21600 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21617 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21617
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21620 =
              FStar_List.map
                (fun uu____21630  ->
                   match uu____21630 with
                   | (uu____21635,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21620 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21640 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21640 imps
let new_t_problem:
  'Auu____21655 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21655 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21655)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21689 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21689
                then
                  let uu____21690 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21691 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21690
                    (rel_to_string rel) uu____21691
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
            let uu____21719 =
              let uu____21722 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21722 in
            FStar_Syntax_Syntax.new_bv uu____21719 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21731 =
              let uu____21734 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_94  -> FStar_Pervasives_Native.Some _0_94)
                uu____21734 in
            let uu____21737 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21731 uu____21737 in
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
          let uu____21770 = FStar_Options.eager_inference () in
          if uu____21770
          then
            let uu___205_21771 = probs in
            {
              attempting = (uu___205_21771.attempting);
              wl_deferred = (uu___205_21771.wl_deferred);
              ctr = (uu___205_21771.ctr);
              defer_ok = false;
              smt_ok = (uu___205_21771.smt_ok);
              tcenv = (uu___205_21771.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____21783 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21783
              then
                let uu____21784 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21784
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
          ((let uu____21796 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21796
            then
              let uu____21797 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21797
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21801 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21801
             then
               let uu____21802 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21802
             else ());
            (let f2 =
               let uu____21805 =
                 let uu____21806 = FStar_Syntax_Util.unmeta f1 in
                 uu____21806.FStar_Syntax_Syntax.n in
               match uu____21805 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21810 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___206_21811 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___206_21811.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___206_21811.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___206_21811.FStar_TypeChecker_Env.implicits)
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
            let uu____21833 =
              let uu____21834 =
                let uu____21835 =
                  let uu____21836 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21836
                    (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21835;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21834 in
            FStar_All.pipe_left
              (fun _0_96  -> FStar_Pervasives_Native.Some _0_96) uu____21833
let with_guard_no_simp:
  'Auu____21867 .
    'Auu____21867 ->
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
            let uu____21887 =
              let uu____21888 =
                let uu____21889 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21889
                  (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21888;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21887
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
          (let uu____21931 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21931
           then
             let uu____21932 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21933 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21932
               uu____21933
           else ());
          (let prob =
             let uu____21936 =
               let uu____21941 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21941 in
             FStar_All.pipe_left
               (fun _0_98  -> FStar_TypeChecker_Common.TProb _0_98)
               uu____21936 in
           let g =
             let uu____21949 =
               let uu____21952 = singleton' env prob smt_ok in
               solve_and_commit env uu____21952
                 (fun uu____21954  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21949 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21975 = try_teq true env t1 t2 in
        match uu____21975 with
        | FStar_Pervasives_Native.None  ->
            let uu____21978 =
              let uu____21979 =
                let uu____21984 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21985 = FStar_TypeChecker_Env.get_range env in
                (uu____21984, uu____21985) in
              FStar_Errors.Error uu____21979 in
            FStar_Exn.raise uu____21978
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21988 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21988
              then
                let uu____21989 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21990 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21991 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21989
                  uu____21990 uu____21991
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
          (let uu____22012 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22012
           then
             let uu____22013 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____22014 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____22013
               uu____22014
           else ());
          (let uu____22016 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____22016 with
           | (prob,x) ->
               let g =
                 let uu____22028 =
                   let uu____22031 = singleton' env prob smt_ok in
                   solve_and_commit env uu____22031
                     (fun uu____22033  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____22028 in
               ((let uu____22043 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____22043
                 then
                   let uu____22044 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____22045 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____22046 =
                     let uu____22047 = FStar_Util.must g in
                     guard_to_string env uu____22047 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____22044 uu____22045 uu____22046
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
          let uu____22079 = FStar_TypeChecker_Env.get_range env in
          let uu____22080 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____22079 uu____22080
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22096 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22096
         then
           let uu____22097 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22098 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22097
             uu____22098
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22103 =
             let uu____22108 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22108 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_99  -> FStar_TypeChecker_Common.CProb _0_99) uu____22103 in
         let uu____22113 =
           let uu____22116 = singleton env prob in
           solve_and_commit env uu____22116
             (fun uu____22118  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22113)
let solve_universe_inequalities':
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____22150  ->
        match uu____22150 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22189 =
                 let uu____22190 =
                   let uu____22195 =
                     let uu____22196 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22197 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22196 uu____22197 in
                   let uu____22198 = FStar_TypeChecker_Env.get_range env in
                   (uu____22195, uu____22198) in
                 FStar_Errors.Error uu____22190 in
               FStar_Exn.raise uu____22189) in
            let equiv1 v1 v' =
              let uu____22206 =
                let uu____22211 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22212 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22211, uu____22212) in
              match uu____22206 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22231 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22261 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22261 with
                      | FStar_Syntax_Syntax.U_unif uu____22268 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22297  ->
                                    match uu____22297 with
                                    | (u,v') ->
                                        let uu____22306 = equiv1 v1 v' in
                                        if uu____22306
                                        then
                                          let uu____22309 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22309 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22325 -> [])) in
            let uu____22330 =
              let wl =
                let uu___207_22334 = empty_worklist env in
                {
                  attempting = (uu___207_22334.attempting);
                  wl_deferred = (uu___207_22334.wl_deferred);
                  ctr = (uu___207_22334.ctr);
                  defer_ok = false;
                  smt_ok = (uu___207_22334.smt_ok);
                  tcenv = (uu___207_22334.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22352  ->
                      match uu____22352 with
                      | (lb,v1) ->
                          let uu____22359 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22359 with
                           | USolved wl1 -> ()
                           | uu____22361 -> fail lb v1))) in
            let rec check_ineq uu____22369 =
              match uu____22369 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22378) -> true
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
                      uu____22401,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22403,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22414) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22421,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22429 -> false) in
            let uu____22434 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22449  ->
                      match uu____22449 with
                      | (u,v1) ->
                          let uu____22456 = check_ineq (u, v1) in
                          if uu____22456
                          then true
                          else
                            ((let uu____22459 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22459
                              then
                                let uu____22460 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22461 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22460
                                  uu____22461
                              else ());
                             false))) in
            if uu____22434
            then ()
            else
              ((let uu____22465 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22465
                then
                  ((let uu____22467 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22467);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22477 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22477))
                else ());
               (let uu____22487 =
                  let uu____22488 =
                    let uu____22493 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22493) in
                  FStar_Errors.Error uu____22488 in
                FStar_Exn.raise uu____22487))
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
      let tx = FStar_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
let rec solve_deferred_constraints:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____22545 =
        match uu____22545 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22559 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22559
       then
         let uu____22560 = wl_to_string wl in
         let uu____22561 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22560 uu____22561
       else ());
      (let g1 =
         let uu____22576 = solve_and_commit env wl fail in
         match uu____22576 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___208_22589 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___208_22589.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___208_22589.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___208_22589.FStar_TypeChecker_Env.implicits)
             }
         | uu____22594 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___209_22598 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___209_22598.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___209_22598.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___209_22598.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22621 = FStar_ST.op_Bang last_proof_ns in
    match uu____22621 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.op_Colon_Equals last_proof_ns
             (FStar_Pervasives_Native.Some pns))
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
            let uu___210_22808 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___210_22808.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___210_22808.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___210_22808.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22809 =
            let uu____22810 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22810 in
          if uu____22809
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22818 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22818
                   then
                     let uu____22819 = FStar_TypeChecker_Env.get_range env in
                     let uu____22820 =
                       let uu____22821 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22821 in
                     FStar_Errors.diag uu____22819 uu____22820
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22824 = check_trivial vc1 in
                   match uu____22824 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22831 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22831
                           then
                             let uu____22832 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22833 =
                               let uu____22834 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22834 in
                             FStar_Errors.diag uu____22832 uu____22833
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22839 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22839
                           then
                             let uu____22840 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22841 =
                               let uu____22842 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22842 in
                             FStar_Errors.diag uu____22840 uu____22841
                           else ());
                          (let vcs =
                             let uu____22853 = FStar_Options.use_tactics () in
                             if uu____22853
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____22863 =
                                  let uu____22870 = FStar_Options.peek () in
                                  (env, vc2, uu____22870) in
                                [uu____22863]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____22904  ->
                                   match uu____22904 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____22915 = check_trivial goal1 in
                                       (match uu____22915 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____22917 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____22917
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____22924 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____22924
                                              then
                                                let uu____22925 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____22926 =
                                                  let uu____22927 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____22928 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____22927 uu____22928 in
                                                FStar_Errors.diag uu____22925
                                                  uu____22926
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2;
                                             FStar_Options.pop ())))));
                          FStar_Pervasives_Native.Some ret_g))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22940 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22940 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22946 =
            let uu____22947 =
              let uu____22952 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22952) in
            FStar_Errors.Error uu____22947 in
          FStar_Exn.raise uu____22946
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22961 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22961 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits':
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun must_total  ->
    fun forcelax  ->
      fun g  ->
        let unresolved u =
          let uu____22983 = FStar_Syntax_Unionfind.find u in
          match uu____22983 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22986 -> false in
        let rec until_fixpoint acc implicits =
          let uu____23004 = acc in
          match uu____23004 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23090 = hd1 in
                   (match uu____23090 with
                    | (uu____23103,env,u,tm,k,r) ->
                        let uu____23109 = unresolved u in
                        if uu____23109
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____23140 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23140
                            then
                              let uu____23141 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23142 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23143 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23141 uu____23142 uu____23143
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___211_23146 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___211_23146.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___211_23146.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___211_23146.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___211_23146.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___211_23146.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___211_23146.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___211_23146.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___211_23146.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___211_23146.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___211_23146.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___211_23146.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___211_23146.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___211_23146.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___211_23146.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___211_23146.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___211_23146.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___211_23146.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___211_23146.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___211_23146.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___211_23146.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___211_23146.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___211_23146.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___211_23146.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___211_23146.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___211_23146.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___211_23146.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___211_23146.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___211_23146.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___211_23146.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___211_23146.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___211_23146.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___211_23146.FStar_TypeChecker_Env.dsenv)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____23149 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___212_23157 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___212_23157.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___212_23157.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___212_23157.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___212_23157.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___212_23157.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___212_23157.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___212_23157.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___212_23157.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___212_23157.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___212_23157.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___212_23157.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___212_23157.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___212_23157.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___212_23157.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___212_23157.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___212_23157.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___212_23157.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___212_23157.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___212_23157.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___212_23157.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___212_23157.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___212_23157.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___212_23157.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___212_23157.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___212_23157.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___212_23157.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___212_23157.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___212_23157.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___212_23157.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___212_23157.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___212_23157.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___212_23157.FStar_TypeChecker_Env.dsenv)
                                     }) tm1 in
                                match uu____23149 with
                                | (uu____23158,uu____23159,g1) -> g1
                              else
                                (let uu____23162 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___213_23170 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___213_23170.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___213_23170.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___213_23170.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___213_23170.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___213_23170.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___213_23170.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___213_23170.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___213_23170.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___213_23170.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___213_23170.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___213_23170.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___213_23170.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___213_23170.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___213_23170.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___213_23170.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___213_23170.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___213_23170.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___213_23170.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___213_23170.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___213_23170.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___213_23170.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___213_23170.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___213_23170.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___213_23170.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___213_23170.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___213_23170.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___213_23170.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___213_23170.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___213_23170.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___213_23170.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___213_23170.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___213_23170.FStar_TypeChecker_Env.dsenv)
                                      }) tm1 in
                                 match uu____23162 with
                                 | (uu____23171,uu____23172,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___214_23175 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___214_23175.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___214_23175.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___214_23175.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23178 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23184  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23178 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___215_23212 = g in
        let uu____23213 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___215_23212.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___215_23212.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___215_23212.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23213
        }
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' true false g
let resolve_implicits_tac:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' false true g
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____23271 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23271 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23284 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23284
      | (reason,uu____23286,uu____23287,e,t,r)::uu____23291 ->
          let uu____23318 =
            let uu____23319 =
              let uu____23324 =
                let uu____23325 = FStar_Syntax_Print.term_to_string t in
                let uu____23326 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23325 uu____23326 in
              (uu____23324, r) in
            FStar_Errors.Error uu____23319 in
          FStar_Exn.raise uu____23318
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___216_23335 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___216_23335.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___216_23335.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___216_23335.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23364 = try_teq false env t1 t2 in
        match uu____23364 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23368 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23368 with
             | FStar_Pervasives_Native.Some uu____23373 -> true
             | FStar_Pervasives_Native.None  -> false)