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
            let uu___141_128 = g1 in
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
                (uu___141_128.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___141_128.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___141_128.FStar_TypeChecker_Env.implicits)
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
          let uu___142_142 = g in
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
              (uu___142_142.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___142_142.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___142_142.FStar_TypeChecker_Env.implicits)
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
          let uu___143_187 = g in
          let uu____188 =
            let uu____189 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____189 in
          {
            FStar_TypeChecker_Env.guard_f = uu____188;
            FStar_TypeChecker_Env.deferred =
              (uu___143_187.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___143_187.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___143_187.FStar_TypeChecker_Env.implicits)
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
            let uu___144_329 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___144_329.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___144_329.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___144_329.FStar_TypeChecker_Env.implicits)
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
            let uu___145_367 = g in
            let uu____368 =
              let uu____369 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____369 in
            {
              FStar_TypeChecker_Env.guard_f = uu____368;
              FStar_TypeChecker_Env.deferred =
                (uu___145_367.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___145_367.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___145_367.FStar_TypeChecker_Env.implicits)
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
  fun uu___113_827  ->
    match uu___113_827 with
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
    fun uu___114_927  ->
      match uu___114_927 with
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
    fun uu___115_962  ->
      match uu___115_962 with
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
        let uu___146_1091 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___146_1091.wl_deferred);
          ctr = (uu___146_1091.ctr);
          defer_ok = (uu___146_1091.defer_ok);
          smt_ok;
          tcenv = (uu___146_1091.tcenv)
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
      let uu___147_1127 = empty_worklist env in
      let uu____1128 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1128;
        wl_deferred = (uu___147_1127.wl_deferred);
        ctr = (uu___147_1127.ctr);
        defer_ok = false;
        smt_ok = (uu___147_1127.smt_ok);
        tcenv = (uu___147_1127.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___148_1145 = wl in
        {
          attempting = (uu___148_1145.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___148_1145.ctr);
          defer_ok = (uu___148_1145.defer_ok);
          smt_ok = (uu___148_1145.smt_ok);
          tcenv = (uu___148_1145.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___149_1164 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___149_1164.wl_deferred);
        ctr = (uu___149_1164.ctr);
        defer_ok = (uu___149_1164.defer_ok);
        smt_ok = (uu___149_1164.smt_ok);
        tcenv = (uu___149_1164.tcenv)
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
  fun uu___116_1184  ->
    match uu___116_1184 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1191 'Auu____1192 .
    ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem ->
      ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___150_1209 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___150_1209.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___150_1209.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___150_1209.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___150_1209.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___150_1209.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___150_1209.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___150_1209.FStar_TypeChecker_Common.rank)
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
  fun uu___117_1242  ->
    match uu___117_1242 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___118_1268  ->
      match uu___118_1268 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___119_1272  ->
    match uu___119_1272 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___120_1286  ->
    match uu___120_1286 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___121_1302  ->
    match uu___121_1302 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___122_1318  ->
    match uu___122_1318 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___123_1336  ->
    match uu___123_1336 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___124_1354  ->
    match uu___124_1354 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___125_1368  ->
    match uu___125_1368 with
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
  'Auu____1469 'Auu____1470 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1470 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1470 ->
              'Auu____1469 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1470,'Auu____1469)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1507 = next_pid () in
                let uu____1508 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1507;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1508;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1531 'Auu____1532 .
    FStar_TypeChecker_Env.env ->
      'Auu____1532 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1532 ->
            'Auu____1531 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1532,'Auu____1531)
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
                let uu____1570 = next_pid () in
                let uu____1571 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1570;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1571;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1592 'Auu____1593 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1593 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1593 ->
            'Auu____1592 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1593,'Auu____1592) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1626 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1626;
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
  'Auu____1637 .
    worklist ->
      ('Auu____1637,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1690 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1690
        then
          let uu____1691 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1692 = prob_to_string env d in
          let uu____1693 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1691 uu____1692 uu____1693 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1699 -> failwith "impossible" in
           let uu____1700 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1714 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1715 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1714, uu____1715)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1721 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1722 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1721, uu____1722) in
           match uu____1700 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___126_1739  ->
            match uu___126_1739 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1751 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1753),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___127_1775  ->
           match uu___127_1775 with
           | UNIV uu____1778 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1784),t) ->
               let uu____1790 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1790
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
        (fun uu___128_1812  ->
           match uu___128_1812 with
           | UNIV (u',t) ->
               let uu____1817 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1817
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1821 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1830 =
        let uu____1831 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1831 in
      FStar_Syntax_Subst.compress uu____1830
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1840 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1840
let norm_arg:
  'Auu____1847 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1847) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1847)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1868 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1868, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1901  ->
              match uu____1901 with
              | (x,imp) ->
                  let uu____1912 =
                    let uu___151_1913 = x in
                    let uu____1914 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___151_1913.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___151_1913.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1914
                    } in
                  (uu____1912, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1931 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1931
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1935 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1935
        | uu____1938 -> u2 in
      let uu____1939 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1939
let normalize_refinement:
  'Auu____1950 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____1950 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement:
  'Auu____1975 .
    FStar_TypeChecker_Env.env ->
      'Auu____1975 ->
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
                (let uu____2080 =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 match uu____2080 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2097;
                     FStar_Syntax_Syntax.vars = uu____2098;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2124 =
                       let uu____2125 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2126 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2125 uu____2126 in
                     failwith uu____2124)
          | FStar_Syntax_Syntax.Tm_uinst uu____2141 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2180 =
                   let uu____2181 = FStar_Syntax_Subst.compress t1' in
                   uu____2181.FStar_Syntax_Syntax.n in
                 match uu____2180 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2198 -> aux true t1'
                 | uu____2205 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2222 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2255 =
                   let uu____2256 = FStar_Syntax_Subst.compress t1' in
                   uu____2256.FStar_Syntax_Syntax.n in
                 match uu____2255 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2273 -> aux true t1'
                 | uu____2280 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2297 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2344 =
                   let uu____2345 = FStar_Syntax_Subst.compress t1' in
                   uu____2345.FStar_Syntax_Syntax.n in
                 match uu____2344 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2362 -> aux true t1'
                 | uu____2369 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2386 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2403 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2420 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2437 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2454 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2483 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2516 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2549 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2578 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2617 ->
              let uu____2624 =
                let uu____2625 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2626 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2625 uu____2626 in
              failwith uu____2624
          | FStar_Syntax_Syntax.Tm_ascribed uu____2641 ->
              let uu____2668 =
                let uu____2669 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2670 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2669 uu____2670 in
              failwith uu____2668
          | FStar_Syntax_Syntax.Tm_delayed uu____2685 ->
              let uu____2710 =
                let uu____2711 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2712 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2711 uu____2712 in
              failwith uu____2710
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2727 =
                let uu____2728 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2729 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2728 uu____2729 in
              failwith uu____2727 in
        let uu____2744 = whnf env t1 in aux false uu____2744
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2755 =
        let uu____2770 = empty_worklist env in
        base_and_refinement env uu____2770 t in
      FStar_All.pipe_right uu____2755 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2805 = FStar_Syntax_Syntax.null_bv t in
    (uu____2805, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2814 .
    FStar_TypeChecker_Env.env ->
      'Auu____2814 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2831 = base_and_refinement env wl t in
        match uu____2831 with
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
  fun uu____2911  ->
    match uu____2911 with
    | (t_base,refopt) ->
        let uu____2938 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2938 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2973 =
      let uu____2976 =
        let uu____2979 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3002  ->
                  match uu____3002 with | (uu____3009,uu____3010,x) -> x)) in
        FStar_List.append wl.attempting uu____2979 in
      FStar_List.map (wl_prob_to_string wl) uu____2976 in
    FStar_All.pipe_right uu____2973 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3038 =
          let uu____3057 =
            let uu____3058 = FStar_Syntax_Subst.compress k in
            uu____3058.FStar_Syntax_Syntax.n in
          match uu____3057 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3123 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3123)
              else
                (let uu____3149 = FStar_Syntax_Util.abs_formals t in
                 match uu____3149 with
                 | (ys',t1,uu____3178) ->
                     let uu____3183 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3183))
          | uu____3224 ->
              let uu____3225 =
                let uu____3236 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3236) in
              ((ys, t), uu____3225) in
        match uu____3038 with
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
                 let uu____3315 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3315 c in
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
            let uu____3348 = p_guard prob in
            match uu____3348 with
            | (uu____3353,uv) ->
                ((let uu____3356 =
                    let uu____3357 = FStar_Syntax_Subst.compress uv in
                    uu____3357.FStar_Syntax_Syntax.n in
                  match uu____3356 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3389 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3389
                        then
                          let uu____3390 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3391 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3392 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3390
                            uu____3391 uu____3392
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3394 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___152_3397 = wl in
                  {
                    attempting = (uu___152_3397.attempting);
                    wl_deferred = (uu___152_3397.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___152_3397.defer_ok);
                    smt_ok = (uu___152_3397.smt_ok);
                    tcenv = (uu___152_3397.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3415 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3415
         then
           let uu____3416 = FStar_Util.string_of_int pid in
           let uu____3417 =
             let uu____3418 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3418 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3416 uu____3417
         else ());
        commit sol;
        (let uu___153_3425 = wl in
         {
           attempting = (uu___153_3425.attempting);
           wl_deferred = (uu___153_3425.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___153_3425.defer_ok);
           smt_ok = (uu___153_3425.smt_ok);
           tcenv = (uu___153_3425.tcenv)
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
            | (uu____3467,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3479 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3479 in
          (let uu____3485 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3485
           then
             let uu____3486 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3487 =
               let uu____3488 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3488 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3486 uu____3487
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
        let uu____3523 =
          let uu____3530 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3530 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3523
          (FStar_Util.for_some
             (fun uu____3566  ->
                match uu____3566 with
                | (uv,uu____3572) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3585 'Auu____3586 .
    'Auu____3586 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3585)
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
            let uu____3618 = occurs wl uk t in Prims.op_Negation uu____3618 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3625 =
                 let uu____3626 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3627 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3626 uu____3627 in
               FStar_Pervasives_Native.Some uu____3625) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3644 'Auu____3645 .
    'Auu____3645 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3644)
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
            let uu____3699 = occurs_check env wl uk t in
            match uu____3699 with
            | (occurs_ok,msg) ->
                let uu____3730 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3730, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3757 'Auu____3758 .
    (FStar_Syntax_Syntax.bv,'Auu____3758) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3757) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3757) FStar_Pervasives_Native.tuple2
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
      let uu____3842 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3896  ->
                fun uu____3897  ->
                  match (uu____3896, uu____3897) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3978 =
                        let uu____3979 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3979 in
                      if uu____3978
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4004 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4004
                         then
                           let uu____4017 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4017)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3842 with | (isect,uu____4058) -> FStar_List.rev isect
let binders_eq:
  'Auu____4087 'Auu____4088 .
    (FStar_Syntax_Syntax.bv,'Auu____4088) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4087) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4143  ->
              fun uu____4144  ->
                match (uu____4143, uu____4144) with
                | ((a,uu____4162),(b,uu____4164)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4183 'Auu____4184 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4184) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4183)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4183)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4235 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4249  ->
                      match uu____4249 with
                      | (b,uu____4255) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4235
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4271 -> FStar_Pervasives_Native.None
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
            let uu____4346 = pat_var_opt env seen hd1 in
            (match uu____4346 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4360 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4360
                   then
                     let uu____4361 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4361
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4380 =
      let uu____4381 = FStar_Syntax_Subst.compress t in
      uu____4381.FStar_Syntax_Syntax.n in
    match uu____4380 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4384 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4401;
           FStar_Syntax_Syntax.pos = uu____4402;
           FStar_Syntax_Syntax.vars = uu____4403;_},uu____4404)
        -> true
    | uu____4441 -> false
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
           FStar_Syntax_Syntax.pos = uu____4566;
           FStar_Syntax_Syntax.vars = uu____4567;_},args)
        -> (t, uv, k, args)
    | uu____4635 -> failwith "Not a flex-uvar"
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
      let uu____4714 = destruct_flex_t t in
      match uu____4714 with
      | (t1,uv,k,args) ->
          let uu____4829 = pat_vars env [] args in
          (match uu____4829 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4927 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5009 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5046 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5051 -> false
let head_match: match_result -> match_result =
  fun uu___129_5055  ->
    match uu___129_5055 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5070 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5081 ->
          let uu____5082 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5082 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5093 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5114 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5123 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5150 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5151 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5152 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5169 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5182 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5206) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5212,uu____5213) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5255) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5276;
             FStar_Syntax_Syntax.index = uu____5277;
             FStar_Syntax_Syntax.sort = t2;_},uu____5279)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5286 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5287 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5288 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5301 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5319 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5319
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
            let uu____5343 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5343
            then FullMatch
            else
              (let uu____5345 =
                 let uu____5354 =
                   let uu____5357 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5357 in
                 let uu____5358 =
                   let uu____5361 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5361 in
                 (uu____5354, uu____5358) in
               MisMatch uu____5345)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5367),FStar_Syntax_Syntax.Tm_uinst (g,uu____5369)) ->
            let uu____5378 = head_matches env f g in
            FStar_All.pipe_right uu____5378 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5387),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5389)) ->
            let uu____5438 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5438
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5445),FStar_Syntax_Syntax.Tm_refine (y,uu____5447)) ->
            let uu____5456 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5456 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5458),uu____5459) ->
            let uu____5464 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5464 head_match
        | (uu____5465,FStar_Syntax_Syntax.Tm_refine (x,uu____5467)) ->
            let uu____5472 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5472 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5473,FStar_Syntax_Syntax.Tm_type
           uu____5474) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5475,FStar_Syntax_Syntax.Tm_arrow uu____5476) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5502),FStar_Syntax_Syntax.Tm_app (head',uu____5504))
            ->
            let uu____5545 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5545 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5547),uu____5548) ->
            let uu____5569 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5569 head_match
        | (uu____5570,FStar_Syntax_Syntax.Tm_app (head1,uu____5572)) ->
            let uu____5593 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5593 head_match
        | uu____5594 ->
            let uu____5599 =
              let uu____5608 = delta_depth_of_term env t11 in
              let uu____5611 = delta_depth_of_term env t21 in
              (uu____5608, uu____5611) in
            MisMatch uu____5599
let head_matches_delta:
  'Auu____5628 .
    FStar_TypeChecker_Env.env ->
      'Auu____5628 ->
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
            let uu____5661 = FStar_Syntax_Util.head_and_args t in
            match uu____5661 with
            | (head1,uu____5679) ->
                let uu____5700 =
                  let uu____5701 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5701.FStar_Syntax_Syntax.n in
                (match uu____5700 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5707 =
                       let uu____5708 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5708 FStar_Option.isSome in
                     if uu____5707
                     then
                       let uu____5727 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5727
                         (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                     else FStar_Pervasives_Native.None
                 | uu____5731 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5834)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5852 =
                     let uu____5861 = maybe_inline t11 in
                     let uu____5864 = maybe_inline t21 in
                     (uu____5861, uu____5864) in
                   match uu____5852 with
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
                (uu____5901,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5919 =
                     let uu____5928 = maybe_inline t11 in
                     let uu____5931 = maybe_inline t21 in
                     (uu____5928, uu____5931) in
                   match uu____5919 with
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
                let uu____5974 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5974 with
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
                let uu____5997 =
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
                (match uu____5997 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6021 -> fail r
            | uu____6030 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6064 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6102 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___130_6116  ->
    match uu___130_6116 with
    | T (t,uu____6118) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6136 = FStar_Syntax_Util.type_u () in
      match uu____6136 with
      | (t,uu____6142) ->
          let uu____6143 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6143
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6156 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6156 FStar_Pervasives_Native.fst
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
        let uu____6222 = head_matches env t1 t' in
        match uu____6222 with
        | MisMatch uu____6223 -> false
        | uu____6232 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6328,imp),T (t2,uu____6331)) -> (t2, imp)
                     | uu____6350 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6417  ->
                    match uu____6417 with
                    | (t2,uu____6431) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6474 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6474 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6549))::tcs2) ->
                       aux
                         (((let uu___154_6584 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___154_6584.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___154_6584.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6602 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___131_6655 =
                 match uu___131_6655 with
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
               let uu____6772 = decompose1 [] bs1 in
               (rebuild, matches, uu____6772))
      | uu____6821 ->
          let rebuild uu___132_6827 =
            match uu___132_6827 with
            | [] -> t1
            | uu____6830 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___133_6862  ->
    match uu___133_6862 with
    | T (t,uu____6864) -> t
    | uu____6873 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___134_6877  ->
    match uu___134_6877 with
    | T (t,uu____6879) -> FStar_Syntax_Syntax.as_arg t
    | uu____6888 -> failwith "Impossible"
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
              | (uu____6999,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7024 = new_uvar r scope1 k in
                  (match uu____7024 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7042 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7059 =
                         let uu____7060 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_48  ->
                              FStar_TypeChecker_Common.TProb _0_48)
                           uu____7060 in
                       ((T (gi_xs, mk_kind)), uu____7059))
              | (uu____7073,uu____7074,C uu____7075) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7222 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7239;
                         FStar_Syntax_Syntax.vars = uu____7240;_})
                        ->
                        let uu____7263 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7263 with
                         | (T (gi_xs,uu____7287),prob) ->
                             let uu____7297 =
                               let uu____7298 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_49  -> C _0_49)
                                 uu____7298 in
                             (uu____7297, [prob])
                         | uu____7301 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7316;
                         FStar_Syntax_Syntax.vars = uu____7317;_})
                        ->
                        let uu____7340 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7340 with
                         | (T (gi_xs,uu____7364),prob) ->
                             let uu____7374 =
                               let uu____7375 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____7375 in
                             (uu____7374, [prob])
                         | uu____7378 -> failwith "impossible")
                    | (uu____7389,uu____7390,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7392;
                         FStar_Syntax_Syntax.vars = uu____7393;_})
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
                        let uu____7524 =
                          let uu____7533 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7533 FStar_List.unzip in
                        (match uu____7524 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7587 =
                                 let uu____7588 =
                                   let uu____7591 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7591 un_T in
                                 let uu____7592 =
                                   let uu____7601 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7601
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7588;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7592;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7587 in
                             ((C gi_xs), sub_probs))
                    | uu____7610 ->
                        let uu____7623 = sub_prob scope1 args q in
                        (match uu____7623 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7222 with
                   | (tc,probs) ->
                       let uu____7654 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7717,uu____7718),T
                            (t,uu____7720)) ->
                             let b1 =
                               ((let uu___155_7757 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___155_7757.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___155_7757.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7758 =
                               let uu____7765 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7765 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7758)
                         | uu____7800 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7654 with
                        | (bopt,scope2,args1) ->
                            let uu____7884 = aux scope2 args1 qs2 in
                            (match uu____7884 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7921 =
                                         let uu____7924 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7924 in
                                       FStar_Syntax_Util.mk_conj_l uu____7921
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7947 =
                                         let uu____7950 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7951 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7950 :: uu____7951 in
                                       FStar_Syntax_Util.mk_conj_l uu____7947 in
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
  'Auu____8022 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8022)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8022)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___156_8043 = p in
      let uu____8048 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8049 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___156_8043.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8048;
        FStar_TypeChecker_Common.relation =
          (uu___156_8043.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8049;
        FStar_TypeChecker_Common.element =
          (uu___156_8043.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___156_8043.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___156_8043.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___156_8043.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___156_8043.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___156_8043.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8063 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8063
            (fun _0_51  -> FStar_TypeChecker_Common.TProb _0_51)
      | FStar_TypeChecker_Common.CProb uu____8072 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8094 = compress_prob wl pr in
        FStar_All.pipe_right uu____8094 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8104 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8104 with
           | (lh,uu____8124) ->
               let uu____8145 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8145 with
                | (rh,uu____8165) ->
                    let uu____8186 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8203,FStar_Syntax_Syntax.Tm_uvar uu____8204)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8241,uu____8242)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8263,FStar_Syntax_Syntax.Tm_uvar uu____8264)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8285,uu____8286)
                          ->
                          let uu____8303 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8303 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8366 ->
                                    let rank =
                                      let uu____8376 = is_top_level_prob prob in
                                      if uu____8376
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8378 =
                                      let uu___157_8383 = tp in
                                      let uu____8388 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___157_8383.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___157_8383.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___157_8383.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8388;
                                        FStar_TypeChecker_Common.element =
                                          (uu___157_8383.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___157_8383.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___157_8383.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___157_8383.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___157_8383.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___157_8383.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8378)))
                      | (uu____8403,FStar_Syntax_Syntax.Tm_uvar uu____8404)
                          ->
                          let uu____8421 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8421 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8484 ->
                                    let uu____8493 =
                                      let uu___158_8500 = tp in
                                      let uu____8505 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___158_8500.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8505;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___158_8500.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___158_8500.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___158_8500.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___158_8500.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___158_8500.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___158_8500.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___158_8500.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___158_8500.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8493)))
                      | (uu____8526,uu____8527) -> (rigid_rigid, tp) in
                    (match uu____8186 with
                     | (rank,tp1) ->
                         let uu____8546 =
                           FStar_All.pipe_right
                             (let uu___159_8552 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___159_8552.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___159_8552.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___159_8552.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___159_8552.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___159_8552.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___159_8552.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___159_8552.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___159_8552.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___159_8552.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_52  ->
                                FStar_TypeChecker_Common.TProb _0_52) in
                         (rank, uu____8546))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8562 =
            FStar_All.pipe_right
              (let uu___160_8568 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___160_8568.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___160_8568.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___160_8568.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___160_8568.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___160_8568.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___160_8568.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___160_8568.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___160_8568.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___160_8568.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_53  -> FStar_TypeChecker_Common.CProb _0_53) in
          (rigid_rigid, uu____8562)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8624 probs =
      match uu____8624 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8677 = rank wl hd1 in
               (match uu____8677 with
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
    match projectee with | UDeferred _0 -> true | uu____8787 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8801 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8815 -> false
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
                        let uu____8860 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8860 with
                        | (k,uu____8866) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8876 -> false)))
            | uu____8877 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8928 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8928 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8931 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8941 =
                     let uu____8942 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8943 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8942
                       uu____8943 in
                   UFailed uu____8941)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8963 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8963 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8985 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8985 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8988 ->
                let uu____8993 =
                  let uu____8994 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8995 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8994
                    uu____8995 msg in
                UFailed uu____8993 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8996,uu____8997) ->
              let uu____8998 =
                let uu____8999 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9000 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8999 uu____9000 in
              failwith uu____8998
          | (FStar_Syntax_Syntax.U_unknown ,uu____9001) ->
              let uu____9002 =
                let uu____9003 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9004 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9003 uu____9004 in
              failwith uu____9002
          | (uu____9005,FStar_Syntax_Syntax.U_bvar uu____9006) ->
              let uu____9007 =
                let uu____9008 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9009 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9008 uu____9009 in
              failwith uu____9007
          | (uu____9010,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9011 =
                let uu____9012 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9013 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9012 uu____9013 in
              failwith uu____9011
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9037 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9037
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9059 = occurs_univ v1 u3 in
              if uu____9059
              then
                let uu____9060 =
                  let uu____9061 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9062 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9061 uu____9062 in
                try_umax_components u11 u21 uu____9060
              else
                (let uu____9064 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9064)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9084 = occurs_univ v1 u3 in
              if uu____9084
              then
                let uu____9085 =
                  let uu____9086 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9087 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9086 uu____9087 in
                try_umax_components u11 u21 uu____9085
              else
                (let uu____9089 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9089)
          | (FStar_Syntax_Syntax.U_max uu____9098,uu____9099) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9105 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9105
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9107,FStar_Syntax_Syntax.U_max uu____9108) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9114 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9114
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9116,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9117,FStar_Syntax_Syntax.U_name
             uu____9118) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9119) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9120) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9121,FStar_Syntax_Syntax.U_succ
             uu____9122) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9123,FStar_Syntax_Syntax.U_zero
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
      let uu____9217 = bc1 in
      match uu____9217 with
      | (bs1,mk_cod1) ->
          let uu____9258 = bc2 in
          (match uu____9258 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9328 = FStar_Util.first_N n1 bs in
                 match uu____9328 with
                 | (bs3,rest) ->
                     let uu____9353 = mk_cod rest in (bs3, uu____9353) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9382 =
                   let uu____9389 = mk_cod1 [] in (bs1, uu____9389) in
                 let uu____9392 =
                   let uu____9399 = mk_cod2 [] in (bs2, uu____9399) in
                 (uu____9382, uu____9392)
               else
                 if l1 > l2
                 then
                   (let uu____9441 = curry l2 bs1 mk_cod1 in
                    let uu____9454 =
                      let uu____9461 = mk_cod2 [] in (bs2, uu____9461) in
                    (uu____9441, uu____9454))
                 else
                   (let uu____9477 =
                      let uu____9484 = mk_cod1 [] in (bs1, uu____9484) in
                    let uu____9487 = curry l1 bs2 mk_cod2 in
                    (uu____9477, uu____9487)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9608 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9608
       then
         let uu____9609 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9609
       else ());
      (let uu____9611 = next_prob probs in
       match uu____9611 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___161_9632 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___161_9632.wl_deferred);
               ctr = (uu___161_9632.ctr);
               defer_ok = (uu___161_9632.defer_ok);
               smt_ok = (uu___161_9632.smt_ok);
               tcenv = (uu___161_9632.tcenv)
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
                  let uu____9643 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9643 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9648 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9648 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9653,uu____9654) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9671 ->
                let uu____9680 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9739  ->
                          match uu____9739 with
                          | (c,uu____9747,uu____9748) -> c < probs.ctr)) in
                (match uu____9680 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9789 =
                            FStar_List.map
                              (fun uu____9804  ->
                                 match uu____9804 with
                                 | (uu____9815,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9789
                      | uu____9818 ->
                          let uu____9827 =
                            let uu___162_9828 = probs in
                            let uu____9829 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9850  ->
                                      match uu____9850 with
                                      | (uu____9857,uu____9858,y) -> y)) in
                            {
                              attempting = uu____9829;
                              wl_deferred = rest;
                              ctr = (uu___162_9828.ctr);
                              defer_ok = (uu___162_9828.defer_ok);
                              smt_ok = (uu___162_9828.smt_ok);
                              tcenv = (uu___162_9828.tcenv)
                            } in
                          solve env uu____9827))))
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
            let uu____9865 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9865 with
            | USolved wl1 ->
                let uu____9867 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9867
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
                  let uu____9913 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9913 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9916 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9928;
                  FStar_Syntax_Syntax.vars = uu____9929;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9932;
                  FStar_Syntax_Syntax.vars = uu____9933;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9947,uu____9948) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9955,FStar_Syntax_Syntax.Tm_uinst uu____9956) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9963 -> USolved wl
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
            ((let uu____9973 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9973
              then
                let uu____9974 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9974 msg
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
        (let uu____9983 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9983
         then
           let uu____9984 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9984
         else ());
        (let uu____9986 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9986 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10048 = head_matches_delta env () t1 t2 in
               match uu____10048 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10089 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10138 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10153 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10154 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10153, uu____10154)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10159 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10160 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10159, uu____10160) in
                        (match uu____10138 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10186 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_54  ->
                                    FStar_TypeChecker_Common.TProb _0_54)
                                 uu____10186 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10217 =
                                    let uu____10226 =
                                      let uu____10229 =
                                        let uu____10232 =
                                          let uu____10233 =
                                            let uu____10240 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10240) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10233 in
                                        FStar_Syntax_Syntax.mk uu____10232 in
                                      uu____10229
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10248 =
                                      let uu____10251 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10251] in
                                    (uu____10226, uu____10248) in
                                  FStar_Pervasives_Native.Some uu____10217
                              | (uu____10264,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10266)) ->
                                  let uu____10271 =
                                    let uu____10278 =
                                      let uu____10281 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10281] in
                                    (t11, uu____10278) in
                                  FStar_Pervasives_Native.Some uu____10271
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10291),uu____10292) ->
                                  let uu____10297 =
                                    let uu____10304 =
                                      let uu____10307 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10307] in
                                    (t21, uu____10304) in
                                  FStar_Pervasives_Native.Some uu____10297
                              | uu____10316 ->
                                  let uu____10321 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10321 with
                                   | (head1,uu____10345) ->
                                       let uu____10366 =
                                         let uu____10367 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10367.FStar_Syntax_Syntax.n in
                                       (match uu____10366 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10378;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10380;_}
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
                                        | uu____10387 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10400) ->
                  let uu____10425 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___135_10451  ->
                            match uu___135_10451 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10458 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10458 with
                                      | (u',uu____10474) ->
                                          let uu____10495 =
                                            let uu____10496 = whnf env u' in
                                            uu____10496.FStar_Syntax_Syntax.n in
                                          (match uu____10495 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10500) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10525 -> false))
                                 | uu____10526 -> false)
                            | uu____10529 -> false)) in
                  (match uu____10425 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10563 tps =
                         match uu____10563 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10611 =
                                    let uu____10620 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10620 in
                                  (match uu____10611 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10655 -> FStar_Pervasives_Native.None) in
                       let uu____10664 =
                         let uu____10673 =
                           let uu____10680 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10680, []) in
                         make_lower_bound uu____10673 lower_bounds in
                       (match uu____10664 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10692 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10692
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
                            ((let uu____10712 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10712
                              then
                                let wl' =
                                  let uu___163_10714 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___163_10714.wl_deferred);
                                    ctr = (uu___163_10714.ctr);
                                    defer_ok = (uu___163_10714.defer_ok);
                                    smt_ok = (uu___163_10714.smt_ok);
                                    tcenv = (uu___163_10714.tcenv)
                                  } in
                                let uu____10715 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10715
                              else ());
                             (let uu____10717 =
                                solve_t env eq_prob
                                  (let uu___164_10719 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___164_10719.wl_deferred);
                                     ctr = (uu___164_10719.ctr);
                                     defer_ok = (uu___164_10719.defer_ok);
                                     smt_ok = (uu___164_10719.smt_ok);
                                     tcenv = (uu___164_10719.tcenv)
                                   }) in
                              match uu____10717 with
                              | Success uu____10722 ->
                                  let wl1 =
                                    let uu___165_10724 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___165_10724.wl_deferred);
                                      ctr = (uu___165_10724.ctr);
                                      defer_ok = (uu___165_10724.defer_ok);
                                      smt_ok = (uu___165_10724.smt_ok);
                                      tcenv = (uu___165_10724.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10726 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10731 -> FStar_Pervasives_Native.None))))
              | uu____10732 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10741 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10741
         then
           let uu____10742 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10742
         else ());
        (let uu____10744 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10744 with
         | (u,args) ->
             let uu____10783 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10783 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10824 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10824 with
                    | (h1,args1) ->
                        let uu____10865 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10865 with
                         | (h2,uu____10885) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10912 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10912
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10930 =
                                          let uu____10933 =
                                            let uu____10934 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_55  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_55) uu____10934 in
                                          [uu____10933] in
                                        FStar_Pervasives_Native.Some
                                          uu____10930))
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
                                       (let uu____10967 =
                                          let uu____10970 =
                                            let uu____10971 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____10971 in
                                          [uu____10970] in
                                        FStar_Pervasives_Native.Some
                                          uu____10967))
                                  else FStar_Pervasives_Native.None
                              | uu____10985 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11075 =
                               let uu____11084 =
                                 let uu____11087 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11087 in
                               (uu____11084, m1) in
                             FStar_Pervasives_Native.Some uu____11075)
                    | (uu____11100,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11102)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11150),uu____11151) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11198 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11251) ->
                       let uu____11276 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___136_11302  ->
                                 match uu___136_11302 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11309 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11309 with
                                           | (u',uu____11325) ->
                                               let uu____11346 =
                                                 let uu____11347 =
                                                   whnf env u' in
                                                 uu____11347.FStar_Syntax_Syntax.n in
                                               (match uu____11346 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11351) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11376 -> false))
                                      | uu____11377 -> false)
                                 | uu____11380 -> false)) in
                       (match uu____11276 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11418 tps =
                              match uu____11418 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11480 =
                                         let uu____11491 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11491 in
                                       (match uu____11480 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11542 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11553 =
                              let uu____11564 =
                                let uu____11573 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11573, []) in
                              make_upper_bound uu____11564 upper_bounds in
                            (match uu____11553 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11587 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11587
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
                                 ((let uu____11613 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11613
                                   then
                                     let wl' =
                                       let uu___166_11615 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___166_11615.wl_deferred);
                                         ctr = (uu___166_11615.ctr);
                                         defer_ok = (uu___166_11615.defer_ok);
                                         smt_ok = (uu___166_11615.smt_ok);
                                         tcenv = (uu___166_11615.tcenv)
                                       } in
                                     let uu____11616 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11616
                                   else ());
                                  (let uu____11618 =
                                     solve_t env eq_prob
                                       (let uu___167_11620 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___167_11620.wl_deferred);
                                          ctr = (uu___167_11620.ctr);
                                          defer_ok =
                                            (uu___167_11620.defer_ok);
                                          smt_ok = (uu___167_11620.smt_ok);
                                          tcenv = (uu___167_11620.tcenv)
                                        }) in
                                   match uu____11618 with
                                   | Success uu____11623 ->
                                       let wl1 =
                                         let uu___168_11625 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___168_11625.wl_deferred);
                                           ctr = (uu___168_11625.ctr);
                                           defer_ok =
                                             (uu___168_11625.defer_ok);
                                           smt_ok = (uu___168_11625.smt_ok);
                                           tcenv = (uu___168_11625.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11627 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11632 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11633 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11724 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11724
                      then
                        let uu____11725 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11725
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___169_11779 = hd1 in
                      let uu____11780 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___169_11779.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___169_11779.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11780
                      } in
                    let hd21 =
                      let uu___170_11784 = hd2 in
                      let uu____11785 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___170_11784.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___170_11784.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11785
                      } in
                    let prob =
                      let uu____11789 =
                        let uu____11794 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11794 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_57  -> FStar_TypeChecker_Common.TProb _0_57)
                        uu____11789 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11805 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11805 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11809 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11809 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11839 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11844 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11839 uu____11844 in
                         ((let uu____11854 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11854
                           then
                             let uu____11855 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11856 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11855 uu____11856
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11879 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11889 = aux scope env [] bs1 bs2 in
              match uu____11889 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11913 = compress_tprob wl problem in
        solve_t' env uu____11913 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11946 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11946 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11977,uu____11978) ->
                   let rec may_relate head3 =
                     let uu____12003 =
                       let uu____12004 = FStar_Syntax_Subst.compress head3 in
                       uu____12004.FStar_Syntax_Syntax.n in
                     match uu____12003 with
                     | FStar_Syntax_Syntax.Tm_name uu____12007 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12008 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12033,uu____12034) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12076) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12082) ->
                         may_relate t
                     | uu____12087 -> false in
                   let uu____12088 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12088
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
                                let uu____12105 =
                                  let uu____12106 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12106 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12105 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12108 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12108
                   else
                     (let uu____12110 =
                        let uu____12111 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12112 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12111 uu____12112 in
                      giveup env1 uu____12110 orig)
               | (uu____12113,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___171_12127 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___171_12127.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___171_12127.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___171_12127.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___171_12127.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___171_12127.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___171_12127.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___171_12127.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___171_12127.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12128,FStar_Pervasives_Native.None ) ->
                   ((let uu____12140 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12140
                     then
                       let uu____12141 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12142 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12143 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12144 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12141
                         uu____12142 uu____12143 uu____12144
                     else ());
                    (let uu____12146 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12146 with
                     | (head11,args1) ->
                         let uu____12183 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12183 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12237 =
                                  let uu____12238 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12239 = args_to_string args1 in
                                  let uu____12240 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12241 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12238 uu____12239 uu____12240
                                    uu____12241 in
                                giveup env1 uu____12237 orig
                              else
                                (let uu____12243 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12249 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12249 = FStar_Syntax_Util.Equal) in
                                 if uu____12243
                                 then
                                   let uu____12250 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12250 with
                                   | USolved wl2 ->
                                       let uu____12252 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12252
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12256 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12256 with
                                    | (base1,refinement1) ->
                                        let uu____12293 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12293 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12374 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12374 with
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
                                                           (fun uu____12396 
                                                              ->
                                                              fun uu____12397
                                                                 ->
                                                                match 
                                                                  (uu____12396,
                                                                    uu____12397)
                                                                with
                                                                | ((a,uu____12415),
                                                                   (a',uu____12417))
                                                                    ->
                                                                    let uu____12426
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
                                                                    uu____12426)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12436 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12436 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12442 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___172_12490 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___172_12490.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12529 =
          match uu____12529 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12745  ->
                              match uu____12745 with
                              | (x,imp) ->
                                  let uu____12756 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12756, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12769 = FStar_Syntax_Util.type_u () in
                      match uu____12769 with
                      | (t1,uu____12775) ->
                          let uu____12776 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12776 in
                    let uu____12781 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12781 with
                     | (t',tm_u1) ->
                         let uu____12794 = destruct_flex_t t' in
                         (match uu____12794 with
                          | (uu____12831,u1,k1,uu____12834) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12893 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12893 in
                              let sol =
                                let uu____12897 =
                                  let uu____12906 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12906) in
                                TERM uu____12897 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13042 = pat_var_opt env pat_args hd1 in
                    (match uu____13042 with
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
                                    (fun uu____13105  ->
                                       match uu____13105 with
                                       | (x,uu____13111) ->
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
                            let uu____13126 =
                              let uu____13127 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____13127 in
                            if uu____13126
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____13139 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____13139 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____13154::uu____13155) ->
                    let uu____13186 =
                      let uu____13199 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13199 in
                    (match uu____13186 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13238 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13245::uu____13246,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13281 =
                let uu____13294 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13294 in
              (match uu____13281 with
               | (all_formals,res_t) ->
                   let uu____13319 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13319 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13353 = lhs in
          match uu____13353 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13363 ->
                    let uu____13364 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13364 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13393 = p in
          match uu____13393 with
          | (((u,k),xs,c),ps,(h,uu____13404,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13486 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13486 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13509 = h gs_xs in
                     let uu____13510 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59) in
                     FStar_Syntax_Util.abs xs1 uu____13509 uu____13510 in
                   ((let uu____13516 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13516
                     then
                       let uu____13517 =
                         let uu____13520 =
                           let uu____13521 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13521
                             (FStar_String.concat "\n\t") in
                         let uu____13526 =
                           let uu____13529 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13530 =
                             let uu____13533 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13534 =
                               let uu____13537 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13538 =
                                 let uu____13541 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13542 =
                                   let uu____13545 =
                                     let uu____13546 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13546
                                       (FStar_String.concat ", ") in
                                   let uu____13551 =
                                     let uu____13554 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13554] in
                                   uu____13545 :: uu____13551 in
                                 uu____13541 :: uu____13542 in
                               uu____13537 :: uu____13538 in
                             uu____13533 :: uu____13534 in
                           uu____13529 :: uu____13530 in
                         uu____13520 :: uu____13526 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13517
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___137_13575 =
          match uu___137_13575 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13607 = p in
          match uu____13607 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13698 = FStar_List.nth ps i in
              (match uu____13698 with
               | (pi,uu____13702) ->
                   let uu____13707 = FStar_List.nth xs i in
                   (match uu____13707 with
                    | (xi,uu____13719) ->
                        let rec gs k =
                          let uu____13732 =
                            let uu____13745 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13745 in
                          match uu____13732 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13820)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13833 = new_uvar r xs k_a in
                                    (match uu____13833 with
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
                                         let uu____13855 = aux subst2 tl1 in
                                         (match uu____13855 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13882 =
                                                let uu____13885 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13885 :: gi_xs' in
                                              let uu____13886 =
                                                let uu____13889 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13889 :: gi_ps' in
                                              (uu____13882, uu____13886))) in
                              aux [] bs in
                        let uu____13894 =
                          let uu____13895 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13895 in
                        if uu____13894
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13899 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13899 with
                           | (g_xs,uu____13911) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13922 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13923 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_60  ->
                                        FStar_Pervasives_Native.Some _0_60) in
                                 FStar_Syntax_Util.abs xs uu____13922
                                   uu____13923 in
                               let sub1 =
                                 let uu____13929 =
                                   let uu____13934 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13937 =
                                     let uu____13940 =
                                       FStar_List.map
                                         (fun uu____13955  ->
                                            match uu____13955 with
                                            | (uu____13964,uu____13965,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13940 in
                                   mk_problem (p_scope orig) orig uu____13934
                                     (p_rel orig) uu____13937
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____13929 in
                               ((let uu____13980 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13980
                                 then
                                   let uu____13981 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13982 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13981 uu____13982
                                 else ());
                                (let wl2 =
                                   let uu____13985 =
                                     let uu____13988 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13988 in
                                   solve_prob orig uu____13985
                                     [TERM (u, proj)] wl1 in
                                 let uu____13997 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____13997))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14028 = lhs in
          match uu____14028 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14064 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14064 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14097 =
                        let uu____14144 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14144) in
                      FStar_Pervasives_Native.Some uu____14097
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14288 =
                           let uu____14295 =
                             let uu____14296 = FStar_Syntax_Subst.compress k1 in
                             uu____14296.FStar_Syntax_Syntax.n in
                           (uu____14295, args) in
                         match uu____14288 with
                         | (uu____14307,[]) ->
                             let uu____14310 =
                               let uu____14321 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14321) in
                             FStar_Pervasives_Native.Some uu____14310
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14342,uu____14343) ->
                             let uu____14364 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14364 with
                              | (uv1,uv_args) ->
                                  let uu____14407 =
                                    let uu____14408 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14408.FStar_Syntax_Syntax.n in
                                  (match uu____14407 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14418) ->
                                       let uu____14443 =
                                         pat_vars env [] uv_args in
                                       (match uu____14443 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14470  ->
                                                      let uu____14471 =
                                                        let uu____14472 =
                                                          let uu____14473 =
                                                            let uu____14478 =
                                                              let uu____14479
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14479
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14478 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14473 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14472 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14471)) in
                                            let c1 =
                                              let uu____14489 =
                                                let uu____14490 =
                                                  let uu____14495 =
                                                    let uu____14496 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14496
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14495 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14490 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14489 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14509 =
                                                let uu____14512 =
                                                  let uu____14513 =
                                                    let uu____14516 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14516
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14513 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14512 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14509 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14534 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14539,uu____14540) ->
                             let uu____14559 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14559 with
                              | (uv1,uv_args) ->
                                  let uu____14602 =
                                    let uu____14603 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14603.FStar_Syntax_Syntax.n in
                                  (match uu____14602 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14613) ->
                                       let uu____14638 =
                                         pat_vars env [] uv_args in
                                       (match uu____14638 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14665  ->
                                                      let uu____14666 =
                                                        let uu____14667 =
                                                          let uu____14668 =
                                                            let uu____14673 =
                                                              let uu____14674
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14674
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14673 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14668 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14667 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14666)) in
                                            let c1 =
                                              let uu____14684 =
                                                let uu____14685 =
                                                  let uu____14690 =
                                                    let uu____14691 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14691
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14690 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14685 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14684 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14704 =
                                                let uu____14707 =
                                                  let uu____14708 =
                                                    let uu____14711 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14711
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14708 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14707 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14704 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14729 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14736) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14777 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14777
                                 (fun _0_63  ->
                                    FStar_Pervasives_Native.Some _0_63)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14813 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14813 with
                                  | (args1,rest) ->
                                      let uu____14842 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14842 with
                                       | (xs2,c2) ->
                                           let uu____14855 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14855
                                             (fun uu____14879  ->
                                                match uu____14879 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14919 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14919 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14987 =
                                        let uu____14992 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14992 in
                                      FStar_All.pipe_right uu____14987
                                        (fun _0_64  ->
                                           FStar_Pervasives_Native.Some _0_64))
                         | uu____15007 ->
                             let uu____15014 =
                               let uu____15015 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____15016 =
                                 FStar_Syntax_Print.term_to_string k1 in
                               let uu____15017 =
                                 FStar_Syntax_Print.term_to_string k_uv in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____15015 uu____15016 uu____15017 in
                             failwith uu____15014 in
                       let uu____15024 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15024
                         (fun uu____15079  ->
                            match uu____15079 with
                            | (xs1,c1) ->
                                let uu____15128 =
                                  let uu____15169 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15169) in
                                FStar_Pervasives_Native.Some uu____15128)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15290 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15306 = project orig env wl1 i st in
                     match uu____15306 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15320) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15335 = imitate orig env wl1 st in
                  match uu____15335 with
                  | Failed uu____15340 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15371 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15371 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15396 =
                      let uu____15397 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15397 wl2 in
                    (match uu____15396 with
                     | Failed uu____15398 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15416 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15416 with
                | (hd1,uu____15432) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15453 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15466 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15467 -> true
                     | uu____15484 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15488 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15488
                         then true
                         else
                           ((let uu____15491 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15491
                             then
                               let uu____15492 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____15492
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15512 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15512 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15525 =
                            let uu____15526 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15526 in
                          giveup_or_defer1 orig uu____15525
                        else
                          (let uu____15528 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15528
                           then
                             let uu____15529 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15529
                              then
                                let uu____15530 = subterms args_lhs in
                                imitate' orig env wl1 uu____15530
                              else
                                ((let uu____15535 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15535
                                  then
                                    let uu____15536 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15537 = names_to_string fvs1 in
                                    let uu____15538 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15536 uu____15537 uu____15538
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
                               (let uu____15542 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15542
                                then
                                  ((let uu____15544 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15544
                                    then
                                      let uu____15545 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15546 = names_to_string fvs1 in
                                      let uu____15547 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15545 uu____15546 uu____15547
                                    else ());
                                   (let uu____15549 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15549))
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
                     (let uu____15560 =
                        let uu____15561 = FStar_Syntax_Free.names t1 in
                        check_head uu____15561 t2 in
                      if uu____15560
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15572 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15572
                          then
                            let uu____15573 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15574 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15573 uu____15574
                          else ());
                         (let uu____15582 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15582))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15659 uu____15660 r =
               match (uu____15659, uu____15660) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15858 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15858
                   then
                     let uu____15859 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15859
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15883 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15883
                       then
                         let uu____15884 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15885 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15886 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15887 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15888 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15884 uu____15885 uu____15886 uu____15887
                           uu____15888
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15948 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15948 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15962 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15962 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16016 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16016 in
                                  let uu____16019 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16019 k3)
                           else
                             (let uu____16023 =
                                let uu____16024 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16025 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16026 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16024 uu____16025 uu____16026 in
                              failwith uu____16023) in
                       let uu____16027 =
                         let uu____16036 =
                           let uu____16049 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16049 in
                         match uu____16036 with
                         | (bs,k1') ->
                             let uu____16076 =
                               let uu____16089 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16089 in
                             (match uu____16076 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16119 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      uu____16119 in
                                  let uu____16128 =
                                    let uu____16133 =
                                      let uu____16134 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16134.FStar_Syntax_Syntax.n in
                                    let uu____16137 =
                                      let uu____16138 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16138.FStar_Syntax_Syntax.n in
                                    (uu____16133, uu____16137) in
                                  (match uu____16128 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16149,uu____16150) ->
                                       (k1', [sub_prob])
                                   | (uu____16155,FStar_Syntax_Syntax.Tm_type
                                      uu____16156) -> (k2', [sub_prob])
                                   | uu____16161 ->
                                       let uu____16166 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16166 with
                                        | (t,uu____16180) ->
                                            let uu____16181 = new_uvar r zs t in
                                            (match uu____16181 with
                                             | (k_zs,uu____16195) ->
                                                 let kprob =
                                                   let uu____16197 =
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
                                                          _0_66) uu____16197 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16027 with
                       | (k_u',sub_probs) ->
                           let uu____16218 =
                             let uu____16229 =
                               let uu____16230 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16230 in
                             let uu____16239 =
                               let uu____16242 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16242 in
                             let uu____16245 =
                               let uu____16248 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16248 in
                             (uu____16229, uu____16239, uu____16245) in
                           (match uu____16218 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16267 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16267 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16286 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16286
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16290 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16290 with
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
             let solve_one_pat uu____16343 uu____16344 =
               match (uu____16343, uu____16344) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16462 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16462
                     then
                       let uu____16463 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16464 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16463 uu____16464
                     else ());
                    (let uu____16466 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16466
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16485  ->
                              fun uu____16486  ->
                                match (uu____16485, uu____16486) with
                                | ((a,uu____16504),(t21,uu____16506)) ->
                                    let uu____16515 =
                                      let uu____16520 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16520
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16515
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67))
                           xs args2 in
                       let guard =
                         let uu____16526 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16526 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16541 = occurs_check env wl (u1, k1) t21 in
                        match uu____16541 with
                        | (occurs_ok,uu____16549) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16557 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16557
                            then
                              let sol =
                                let uu____16559 =
                                  let uu____16568 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16568) in
                                TERM uu____16559 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16575 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16575
                               then
                                 let uu____16576 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16576 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16600,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16626 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16626
                                       then
                                         let uu____16627 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16627
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16634 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16636 = lhs in
             match uu____16636 with
             | (t1,u1,k1,args1) ->
                 let uu____16641 = rhs in
                 (match uu____16641 with
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
                       | uu____16681 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16691 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16691 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16709) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16716 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16716
                                    then
                                      let uu____16717 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16717
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16724 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16726 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16726
        then
          let uu____16727 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16727
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16731 = FStar_Util.physical_equality t1 t2 in
           if uu____16731
           then
             let uu____16732 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16732
           else
             ((let uu____16735 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16735
               then
                 let uu____16736 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16736
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16739,uu____16740) ->
                   let uu____16767 =
                     let uu___173_16768 = problem in
                     let uu____16769 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___173_16768.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16769;
                       FStar_TypeChecker_Common.relation =
                         (uu___173_16768.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___173_16768.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___173_16768.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___173_16768.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___173_16768.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___173_16768.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___173_16768.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___173_16768.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16767 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16770,uu____16771) ->
                   let uu____16778 =
                     let uu___173_16779 = problem in
                     let uu____16780 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___173_16779.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16780;
                       FStar_TypeChecker_Common.relation =
                         (uu___173_16779.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___173_16779.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___173_16779.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___173_16779.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___173_16779.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___173_16779.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___173_16779.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___173_16779.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16778 wl
               | (uu____16781,FStar_Syntax_Syntax.Tm_ascribed uu____16782) ->
                   let uu____16809 =
                     let uu___174_16810 = problem in
                     let uu____16811 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___174_16810.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___174_16810.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___174_16810.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16811;
                       FStar_TypeChecker_Common.element =
                         (uu___174_16810.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___174_16810.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___174_16810.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___174_16810.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___174_16810.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___174_16810.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16809 wl
               | (uu____16812,FStar_Syntax_Syntax.Tm_meta uu____16813) ->
                   let uu____16820 =
                     let uu___174_16821 = problem in
                     let uu____16822 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___174_16821.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___174_16821.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___174_16821.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16822;
                       FStar_TypeChecker_Common.element =
                         (uu___174_16821.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___174_16821.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___174_16821.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___174_16821.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___174_16821.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___174_16821.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16820 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16823,uu____16824) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16825,FStar_Syntax_Syntax.Tm_bvar uu____16826) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___138_16881 =
                     match uu___138_16881 with
                     | [] -> c
                     | bs ->
                         let uu____16903 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16903 in
                   let uu____16912 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16912 with
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
                                   let uu____17054 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17054
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17056 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.CProb _0_68)
                                   uu____17056))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___139_17132 =
                     match uu___139_17132 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17166 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17166 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17302 =
                                   let uu____17307 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17308 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17307
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17308 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17302))
               | (FStar_Syntax_Syntax.Tm_abs uu____17313,uu____17314) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17339 -> true
                     | uu____17356 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17390 =
                     let uu____17407 = maybe_eta t1 in
                     let uu____17414 = maybe_eta t2 in
                     (uu____17407, uu____17414) in
                   (match uu____17390 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___175_17456 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___175_17456.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___175_17456.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___175_17456.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___175_17456.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___175_17456.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___175_17456.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___175_17456.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___175_17456.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17479 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17479
                        then
                          let uu____17480 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17480 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17508 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17508
                        then
                          let uu____17509 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17509 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17517 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17534,FStar_Syntax_Syntax.Tm_abs uu____17535) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17560 -> true
                     | uu____17577 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17611 =
                     let uu____17628 = maybe_eta t1 in
                     let uu____17635 = maybe_eta t2 in
                     (uu____17628, uu____17635) in
                   (match uu____17611 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___175_17677 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___175_17677.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___175_17677.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___175_17677.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___175_17677.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___175_17677.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___175_17677.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___175_17677.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___175_17677.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17700 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17700
                        then
                          let uu____17701 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17701 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17729 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17729
                        then
                          let uu____17730 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17730 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17738 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17755,FStar_Syntax_Syntax.Tm_refine uu____17756) ->
                   let uu____17769 = as_refinement env wl t1 in
                   (match uu____17769 with
                    | (x1,phi1) ->
                        let uu____17776 = as_refinement env wl t2 in
                        (match uu____17776 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17784 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_70  ->
                                    FStar_TypeChecker_Common.TProb _0_70)
                                 uu____17784 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17822 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17822
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17826 =
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
                                 let uu____17832 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17832 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17841 =
                                   let uu____17846 =
                                     let uu____17847 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____17847 :: (p_scope orig) in
                                   mk_problem uu____17846 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.TProb _0_71)
                                   uu____17841 in
                               let uu____17852 =
                                 solve env1
                                   (let uu___176_17854 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___176_17854.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___176_17854.smt_ok);
                                      tcenv = (uu___176_17854.tcenv)
                                    }) in
                               (match uu____17852 with
                                | Failed uu____17861 -> fallback ()
                                | Success uu____17866 ->
                                    let guard =
                                      let uu____17870 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17875 =
                                        let uu____17876 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17876
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17870
                                        uu____17875 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___177_17885 = wl1 in
                                      {
                                        attempting =
                                          (uu___177_17885.attempting);
                                        wl_deferred =
                                          (uu___177_17885.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___177_17885.defer_ok);
                                        smt_ok = (uu___177_17885.smt_ok);
                                        tcenv = (uu___177_17885.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17887,FStar_Syntax_Syntax.Tm_uvar uu____17888) ->
                   let uu____17921 = destruct_flex_t t1 in
                   let uu____17922 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17921 uu____17922
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17923;
                     FStar_Syntax_Syntax.pos = uu____17924;
                     FStar_Syntax_Syntax.vars = uu____17925;_},uu____17926),FStar_Syntax_Syntax.Tm_uvar
                  uu____17927) ->
                   let uu____17980 = destruct_flex_t t1 in
                   let uu____17981 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17980 uu____17981
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17982,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17983;
                     FStar_Syntax_Syntax.pos = uu____17984;
                     FStar_Syntax_Syntax.vars = uu____17985;_},uu____17986))
                   ->
                   let uu____18039 = destruct_flex_t t1 in
                   let uu____18040 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18039 uu____18040
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18041;
                     FStar_Syntax_Syntax.pos = uu____18042;
                     FStar_Syntax_Syntax.vars = uu____18043;_},uu____18044),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18045;
                     FStar_Syntax_Syntax.pos = uu____18046;
                     FStar_Syntax_Syntax.vars = uu____18047;_},uu____18048))
                   ->
                   let uu____18121 = destruct_flex_t t1 in
                   let uu____18122 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18121 uu____18122
               | (FStar_Syntax_Syntax.Tm_uvar uu____18123,uu____18124) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18141 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18141 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18148;
                     FStar_Syntax_Syntax.pos = uu____18149;
                     FStar_Syntax_Syntax.vars = uu____18150;_},uu____18151),uu____18152)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18189 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18189 t2 wl
               | (uu____18196,FStar_Syntax_Syntax.Tm_uvar uu____18197) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18214,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18215;
                     FStar_Syntax_Syntax.pos = uu____18216;
                     FStar_Syntax_Syntax.vars = uu____18217;_},uu____18218))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18255,FStar_Syntax_Syntax.Tm_type uu____18256) ->
                   solve_t' env
                     (let uu___178_18274 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18274.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18274.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18274.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18274.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18274.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18274.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18274.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18274.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18274.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18275;
                     FStar_Syntax_Syntax.pos = uu____18276;
                     FStar_Syntax_Syntax.vars = uu____18277;_},uu____18278),FStar_Syntax_Syntax.Tm_type
                  uu____18279) ->
                   solve_t' env
                     (let uu___178_18317 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18317.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18317.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18317.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18317.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18317.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18317.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18317.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18317.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18317.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18318,FStar_Syntax_Syntax.Tm_arrow uu____18319) ->
                   solve_t' env
                     (let uu___178_18349 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18349.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18349.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18349.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18349.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18349.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18349.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18349.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18349.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18349.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18350;
                     FStar_Syntax_Syntax.pos = uu____18351;
                     FStar_Syntax_Syntax.vars = uu____18352;_},uu____18353),FStar_Syntax_Syntax.Tm_arrow
                  uu____18354) ->
                   solve_t' env
                     (let uu___178_18404 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___178_18404.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___178_18404.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___178_18404.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___178_18404.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___178_18404.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___178_18404.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___178_18404.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___178_18404.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___178_18404.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18405,uu____18406) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18425 =
                        let uu____18426 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18426 in
                      if uu____18425
                      then
                        let uu____18427 =
                          FStar_All.pipe_left
                            (fun _0_72  ->
                               FStar_TypeChecker_Common.TProb _0_72)
                            (let uu___179_18433 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___179_18433.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___179_18433.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___179_18433.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___179_18433.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___179_18433.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___179_18433.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___179_18433.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___179_18433.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___179_18433.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18434 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18427 uu____18434 t2
                          wl
                      else
                        (let uu____18442 = base_and_refinement env wl t2 in
                         match uu____18442 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18485 =
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      (let uu___180_18491 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___180_18491.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___180_18491.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___180_18491.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___180_18491.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___180_18491.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___180_18491.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___180_18491.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___180_18491.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___180_18491.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18492 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18485
                                    uu____18492 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___181_18512 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___181_18512.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___181_18512.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18515 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      uu____18515 in
                                  let guard =
                                    let uu____18527 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18527
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18535;
                     FStar_Syntax_Syntax.pos = uu____18536;
                     FStar_Syntax_Syntax.vars = uu____18537;_},uu____18538),uu____18539)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18578 =
                        let uu____18579 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18579 in
                      if uu____18578
                      then
                        let uu____18580 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___179_18586 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___179_18586.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___179_18586.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___179_18586.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___179_18586.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___179_18586.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___179_18586.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___179_18586.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___179_18586.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___179_18586.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18587 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18580 uu____18587 t2
                          wl
                      else
                        (let uu____18595 = base_and_refinement env wl t2 in
                         match uu____18595 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18638 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___180_18644 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___180_18644.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___180_18644.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___180_18644.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___180_18644.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___180_18644.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___180_18644.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___180_18644.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___180_18644.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___180_18644.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18645 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18638
                                    uu____18645 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___181_18665 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___181_18665.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___181_18665.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18668 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____18668 in
                                  let guard =
                                    let uu____18680 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18680
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18688,FStar_Syntax_Syntax.Tm_uvar uu____18689) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18707 = base_and_refinement env wl t1 in
                      match uu____18707 with
                      | (t_base,uu____18723) ->
                          solve_t env
                            (let uu___182_18745 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___182_18745.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___182_18745.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___182_18745.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___182_18745.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___182_18745.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___182_18745.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___182_18745.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___182_18745.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18748,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18749;
                     FStar_Syntax_Syntax.pos = uu____18750;
                     FStar_Syntax_Syntax.vars = uu____18751;_},uu____18752))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18790 = base_and_refinement env wl t1 in
                      match uu____18790 with
                      | (t_base,uu____18806) ->
                          solve_t env
                            (let uu___182_18828 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___182_18828.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___182_18828.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___182_18828.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___182_18828.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___182_18828.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___182_18828.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___182_18828.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___182_18828.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18831,uu____18832) ->
                   let t21 =
                     let uu____18842 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18842 in
                   solve_t env
                     (let uu___183_18866 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___183_18866.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___183_18866.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___183_18866.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___183_18866.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___183_18866.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___183_18866.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___183_18866.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___183_18866.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___183_18866.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18867,FStar_Syntax_Syntax.Tm_refine uu____18868) ->
                   let t11 =
                     let uu____18878 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18878 in
                   solve_t env
                     (let uu___184_18902 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___184_18902.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___184_18902.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___184_18902.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___184_18902.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___184_18902.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___184_18902.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___184_18902.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___184_18902.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___184_18902.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18905,uu____18906) ->
                   let head1 =
                     let uu____18932 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18932
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18976 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18976
                       FStar_Pervasives_Native.fst in
                   let uu____19017 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19017
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19032 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19032
                      then
                        let guard =
                          let uu____19044 =
                            let uu____19045 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19045 = FStar_Syntax_Util.Equal in
                          if uu____19044
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19049 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19049) in
                        let uu____19052 = solve_prob orig guard [] wl in
                        solve env uu____19052
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19055,uu____19056) ->
                   let head1 =
                     let uu____19066 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19066
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19110 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19110
                       FStar_Pervasives_Native.fst in
                   let uu____19151 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19151
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19166 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19166
                      then
                        let guard =
                          let uu____19178 =
                            let uu____19179 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19179 = FStar_Syntax_Util.Equal in
                          if uu____19178
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19183 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19183) in
                        let uu____19186 = solve_prob orig guard [] wl in
                        solve env uu____19186
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19189,uu____19190) ->
                   let head1 =
                     let uu____19194 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19194
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19238 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19238
                       FStar_Pervasives_Native.fst in
                   let uu____19279 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19279
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19294 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19294
                      then
                        let guard =
                          let uu____19306 =
                            let uu____19307 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19307 = FStar_Syntax_Util.Equal in
                          if uu____19306
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19311 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19311) in
                        let uu____19314 = solve_prob orig guard [] wl in
                        solve env uu____19314
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19317,uu____19318) ->
                   let head1 =
                     let uu____19322 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19322
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19366 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19366
                       FStar_Pervasives_Native.fst in
                   let uu____19407 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19407
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19422 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19422
                      then
                        let guard =
                          let uu____19434 =
                            let uu____19435 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19435 = FStar_Syntax_Util.Equal in
                          if uu____19434
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19439 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19439) in
                        let uu____19442 = solve_prob orig guard [] wl in
                        solve env uu____19442
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19445,uu____19446) ->
                   let head1 =
                     let uu____19450 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19450
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19494 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19494
                       FStar_Pervasives_Native.fst in
                   let uu____19535 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19535
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19550 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19550
                      then
                        let guard =
                          let uu____19562 =
                            let uu____19563 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19563 = FStar_Syntax_Util.Equal in
                          if uu____19562
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19567 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19567) in
                        let uu____19570 = solve_prob orig guard [] wl in
                        solve env uu____19570
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19573,uu____19574) ->
                   let head1 =
                     let uu____19592 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19592
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19636 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19636
                       FStar_Pervasives_Native.fst in
                   let uu____19677 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19677
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19692 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19692
                      then
                        let guard =
                          let uu____19704 =
                            let uu____19705 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19705 = FStar_Syntax_Util.Equal in
                          if uu____19704
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19709 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19709) in
                        let uu____19712 = solve_prob orig guard [] wl in
                        solve env uu____19712
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19715,FStar_Syntax_Syntax.Tm_match uu____19716) ->
                   let head1 =
                     let uu____19742 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19742
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19786 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19786
                       FStar_Pervasives_Native.fst in
                   let uu____19827 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19827
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19842 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19842
                      then
                        let guard =
                          let uu____19854 =
                            let uu____19855 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19855 = FStar_Syntax_Util.Equal in
                          if uu____19854
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19859 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19859) in
                        let uu____19862 = solve_prob orig guard [] wl in
                        solve env uu____19862
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19865,FStar_Syntax_Syntax.Tm_uinst uu____19866) ->
                   let head1 =
                     let uu____19876 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19876
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19920 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19920
                       FStar_Pervasives_Native.fst in
                   let uu____19961 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19961
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19976 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19976
                      then
                        let guard =
                          let uu____19988 =
                            let uu____19989 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19989 = FStar_Syntax_Util.Equal in
                          if uu____19988
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19993 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19993) in
                        let uu____19996 = solve_prob orig guard [] wl in
                        solve env uu____19996
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19999,FStar_Syntax_Syntax.Tm_name uu____20000) ->
                   let head1 =
                     let uu____20004 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20004
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20048 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20048
                       FStar_Pervasives_Native.fst in
                   let uu____20089 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20089
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20104 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20104
                      then
                        let guard =
                          let uu____20116 =
                            let uu____20117 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20117 = FStar_Syntax_Util.Equal in
                          if uu____20116
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20121 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20121) in
                        let uu____20124 = solve_prob orig guard [] wl in
                        solve env uu____20124
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20127,FStar_Syntax_Syntax.Tm_constant uu____20128) ->
                   let head1 =
                     let uu____20132 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20132
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20176 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20176
                       FStar_Pervasives_Native.fst in
                   let uu____20217 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20217
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20232 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20232
                      then
                        let guard =
                          let uu____20244 =
                            let uu____20245 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20245 = FStar_Syntax_Util.Equal in
                          if uu____20244
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20249 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20249) in
                        let uu____20252 = solve_prob orig guard [] wl in
                        solve env uu____20252
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20255,FStar_Syntax_Syntax.Tm_fvar uu____20256) ->
                   let head1 =
                     let uu____20260 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20260
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20304 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20304
                       FStar_Pervasives_Native.fst in
                   let uu____20345 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20345
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20360 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20360
                      then
                        let guard =
                          let uu____20372 =
                            let uu____20373 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20373 = FStar_Syntax_Util.Equal in
                          if uu____20372
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20377 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20377) in
                        let uu____20380 = solve_prob orig guard [] wl in
                        solve env uu____20380
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20383,FStar_Syntax_Syntax.Tm_app uu____20384) ->
                   let head1 =
                     let uu____20402 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20402
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20446 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20446
                       FStar_Pervasives_Native.fst in
                   let uu____20487 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20487
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20502 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20502
                      then
                        let guard =
                          let uu____20514 =
                            let uu____20515 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20515 = FStar_Syntax_Util.Equal in
                          if uu____20514
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20519 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_Pervasives_Native.Some _0_89)
                               uu____20519) in
                        let uu____20522 = solve_prob orig guard [] wl in
                        solve env uu____20522
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20525,uu____20526) ->
                   let uu____20539 =
                     let uu____20540 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20541 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20540
                       uu____20541 in
                   failwith uu____20539
               | (FStar_Syntax_Syntax.Tm_delayed uu____20542,uu____20543) ->
                   let uu____20568 =
                     let uu____20569 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20570 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20569
                       uu____20570 in
                   failwith uu____20568
               | (uu____20571,FStar_Syntax_Syntax.Tm_delayed uu____20572) ->
                   let uu____20597 =
                     let uu____20598 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20599 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20598
                       uu____20599 in
                   failwith uu____20597
               | (uu____20600,FStar_Syntax_Syntax.Tm_let uu____20601) ->
                   let uu____20614 =
                     let uu____20615 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20616 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20615
                       uu____20616 in
                   failwith uu____20614
               | uu____20617 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20653 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20653
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20655 =
               let uu____20656 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20657 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20656 uu____20657 in
             giveup env uu____20655 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20677  ->
                    fun uu____20678  ->
                      match (uu____20677, uu____20678) with
                      | ((a1,uu____20696),(a2,uu____20698)) ->
                          let uu____20707 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_90  ->
                               FStar_TypeChecker_Common.TProb _0_90)
                            uu____20707)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20717 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20717 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20741 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20748)::[] -> wp1
              | uu____20765 ->
                  let uu____20774 =
                    let uu____20775 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20775 in
                  failwith uu____20774 in
            let uu____20778 =
              let uu____20787 =
                let uu____20788 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20788 in
              [uu____20787] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20778;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20789 = lift_c1 () in solve_eq uu____20789 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___140_20795  ->
                       match uu___140_20795 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20796 -> false)) in
             let uu____20797 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20831)::uu____20832,(wp2,uu____20834)::uu____20835)
                   -> (wp1, wp2)
               | uu____20892 ->
                   let uu____20913 =
                     let uu____20914 =
                       let uu____20919 =
                         let uu____20920 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20921 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20920 uu____20921 in
                       (uu____20919, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20914 in
                   FStar_Exn.raise uu____20913 in
             match uu____20797 with
             | (wpc1,wpc2) ->
                 let uu____20940 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20940
                 then
                   let uu____20943 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20943 wl
                 else
                   (let uu____20947 =
                      let uu____20954 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20954 in
                    match uu____20947 with
                    | (c2_decl,qualifiers) ->
                        let uu____20975 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20975
                        then
                          let c1_repr =
                            let uu____20979 =
                              let uu____20980 =
                                let uu____20981 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20981 in
                              let uu____20982 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20980 uu____20982 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20979 in
                          let c2_repr =
                            let uu____20984 =
                              let uu____20985 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20986 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20985 uu____20986 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20984 in
                          let prob =
                            let uu____20988 =
                              let uu____20993 =
                                let uu____20994 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20995 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20994
                                  uu____20995 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20993 in
                            FStar_TypeChecker_Common.TProb uu____20988 in
                          let wl1 =
                            let uu____20997 =
                              let uu____21000 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21000 in
                            solve_prob orig uu____20997 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21009 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21009
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____21011 =
                                     let uu____21014 =
                                       let uu____21015 =
                                         let uu____21030 =
                                           let uu____21031 =
                                             let uu____21032 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____21032] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____21031 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21033 =
                                           let uu____21036 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21037 =
                                             let uu____21040 =
                                               let uu____21041 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21041 in
                                             [uu____21040] in
                                           uu____21036 :: uu____21037 in
                                         (uu____21030, uu____21033) in
                                       FStar_Syntax_Syntax.Tm_app uu____21015 in
                                     FStar_Syntax_Syntax.mk uu____21014 in
                                   uu____21011 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____21048 =
                                    let uu____21051 =
                                      let uu____21052 =
                                        let uu____21067 =
                                          let uu____21068 =
                                            let uu____21069 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____21069] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____21068 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21070 =
                                          let uu____21073 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21074 =
                                            let uu____21077 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21078 =
                                              let uu____21081 =
                                                let uu____21082 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21082 in
                                              [uu____21081] in
                                            uu____21077 :: uu____21078 in
                                          uu____21073 :: uu____21074 in
                                        (uu____21067, uu____21070) in
                                      FStar_Syntax_Syntax.Tm_app uu____21052 in
                                    FStar_Syntax_Syntax.mk uu____21051 in
                                  uu____21048 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21089 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_91  ->
                                  FStar_TypeChecker_Common.TProb _0_91)
                               uu____21089 in
                           let wl1 =
                             let uu____21099 =
                               let uu____21102 =
                                 let uu____21105 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21105 g in
                               FStar_All.pipe_left
                                 (fun _0_92  ->
                                    FStar_Pervasives_Native.Some _0_92)
                                 uu____21102 in
                             solve_prob orig uu____21099 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21118 = FStar_Util.physical_equality c1 c2 in
        if uu____21118
        then
          let uu____21119 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21119
        else
          ((let uu____21122 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21122
            then
              let uu____21123 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21124 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21123
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21124
            else ());
           (let uu____21126 =
              let uu____21131 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21132 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21131, uu____21132) in
            match uu____21126 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21136),FStar_Syntax_Syntax.Total
                    (t2,uu____21138)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21155 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21155 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21158,FStar_Syntax_Syntax.Total uu____21159) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21177),FStar_Syntax_Syntax.Total
                    (t2,uu____21179)) ->
                     let uu____21196 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21196 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21200),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21202)) ->
                     let uu____21219 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21219 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21223),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21225)) ->
                     let uu____21242 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21242 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21245,FStar_Syntax_Syntax.Comp uu____21246) ->
                     let uu____21255 =
                       let uu___185_21260 = problem in
                       let uu____21265 =
                         let uu____21266 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21266 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___185_21260.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21265;
                         FStar_TypeChecker_Common.relation =
                           (uu___185_21260.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___185_21260.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___185_21260.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___185_21260.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___185_21260.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___185_21260.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___185_21260.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___185_21260.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21255 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21267,FStar_Syntax_Syntax.Comp uu____21268) ->
                     let uu____21277 =
                       let uu___185_21282 = problem in
                       let uu____21287 =
                         let uu____21288 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21288 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___185_21282.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21287;
                         FStar_TypeChecker_Common.relation =
                           (uu___185_21282.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___185_21282.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___185_21282.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___185_21282.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___185_21282.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___185_21282.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___185_21282.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___185_21282.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21277 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21289,FStar_Syntax_Syntax.GTotal uu____21290) ->
                     let uu____21299 =
                       let uu___186_21304 = problem in
                       let uu____21309 =
                         let uu____21310 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21310 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___186_21304.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___186_21304.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___186_21304.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21309;
                         FStar_TypeChecker_Common.element =
                           (uu___186_21304.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___186_21304.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___186_21304.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___186_21304.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___186_21304.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___186_21304.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21299 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21311,FStar_Syntax_Syntax.Total uu____21312) ->
                     let uu____21321 =
                       let uu___186_21326 = problem in
                       let uu____21331 =
                         let uu____21332 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21332 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___186_21326.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___186_21326.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___186_21326.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21331;
                         FStar_TypeChecker_Common.element =
                           (uu___186_21326.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___186_21326.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___186_21326.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___186_21326.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___186_21326.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___186_21326.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21321 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21333,FStar_Syntax_Syntax.Comp uu____21334) ->
                     let uu____21335 =
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
                     if uu____21335
                     then
                       let uu____21336 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21336 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21342 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21352 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21353 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21352, uu____21353)) in
                          match uu____21342 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21360 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21360
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21362 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21362 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21365 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21367 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21367) in
                                if uu____21365
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
                                  (let uu____21370 =
                                     let uu____21371 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21372 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21371 uu____21372 in
                                   giveup env uu____21370 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21378 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21416  ->
              match uu____21416 with
              | (uu____21429,uu____21430,u,uu____21432,uu____21433,uu____21434)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21378 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21466 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21466 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21484 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21512  ->
                match uu____21512 with
                | (u1,u2) ->
                    let uu____21519 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21520 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21519 uu____21520)) in
      FStar_All.pipe_right uu____21484 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21539,[])) -> "{}"
      | uu____21564 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21581 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21581
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21584 =
              FStar_List.map
                (fun uu____21594  ->
                   match uu____21594 with
                   | (uu____21599,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21584 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21604 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21604 imps
let new_t_problem:
  'Auu____21619 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21619 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21619)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21653 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21653
                then
                  let uu____21654 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21655 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21654
                    (rel_to_string rel) uu____21655
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
            let uu____21683 =
              let uu____21686 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21686 in
            FStar_Syntax_Syntax.new_bv uu____21683 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21695 =
              let uu____21698 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_94  -> FStar_Pervasives_Native.Some _0_94)
                uu____21698 in
            let uu____21701 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21695 uu____21701 in
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
          let uu____21734 = FStar_Options.eager_inference () in
          if uu____21734
          then
            let uu___187_21735 = probs in
            {
              attempting = (uu___187_21735.attempting);
              wl_deferred = (uu___187_21735.wl_deferred);
              ctr = (uu___187_21735.ctr);
              defer_ok = false;
              smt_ok = (uu___187_21735.smt_ok);
              tcenv = (uu___187_21735.tcenv)
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
             (let uu____21747 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21747
              then
                let uu____21748 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21748
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
          ((let uu____21760 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21760
            then
              let uu____21761 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21761
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21765 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21765
             then
               let uu____21766 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21766
             else ());
            (let f2 =
               let uu____21769 =
                 let uu____21770 = FStar_Syntax_Util.unmeta f1 in
                 uu____21770.FStar_Syntax_Syntax.n in
               match uu____21769 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21774 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___188_21775 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___188_21775.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___188_21775.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___188_21775.FStar_TypeChecker_Env.implicits)
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
            let uu____21797 =
              let uu____21798 =
                let uu____21799 =
                  let uu____21800 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21800
                    (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21799;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21798 in
            FStar_All.pipe_left
              (fun _0_96  -> FStar_Pervasives_Native.Some _0_96) uu____21797
let with_guard_no_simp:
  'Auu____21831 .
    'Auu____21831 ->
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
            let uu____21851 =
              let uu____21852 =
                let uu____21853 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21853
                  (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21852;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21851
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
          (let uu____21895 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21895
           then
             let uu____21896 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21897 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21896
               uu____21897
           else ());
          (let prob =
             let uu____21900 =
               let uu____21905 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21905 in
             FStar_All.pipe_left
               (fun _0_98  -> FStar_TypeChecker_Common.TProb _0_98)
               uu____21900 in
           let g =
             let uu____21913 =
               let uu____21916 = singleton' env prob smt_ok in
               solve_and_commit env uu____21916
                 (fun uu____21918  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21913 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21939 = try_teq true env t1 t2 in
        match uu____21939 with
        | FStar_Pervasives_Native.None  ->
            let uu____21942 =
              let uu____21943 =
                let uu____21948 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21949 = FStar_TypeChecker_Env.get_range env in
                (uu____21948, uu____21949) in
              FStar_Errors.Error uu____21943 in
            FStar_Exn.raise uu____21942
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21952 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21952
              then
                let uu____21953 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21954 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21955 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21953
                  uu____21954 uu____21955
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
          (let uu____21976 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21976
           then
             let uu____21977 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21978 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21977
               uu____21978
           else ());
          (let uu____21980 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21980 with
           | (prob,x) ->
               let g =
                 let uu____21992 =
                   let uu____21995 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21995
                     (fun uu____21997  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21992 in
               ((let uu____22007 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____22007
                 then
                   let uu____22008 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____22009 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____22010 =
                     let uu____22011 = FStar_Util.must g in
                     guard_to_string env uu____22011 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____22008 uu____22009 uu____22010
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
          let uu____22043 = FStar_TypeChecker_Env.get_range env in
          let uu____22044 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____22043 uu____22044
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22060 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22060
         then
           let uu____22061 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22062 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22061
             uu____22062
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22067 =
             let uu____22072 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22072 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_99  -> FStar_TypeChecker_Common.CProb _0_99) uu____22067 in
         let uu____22077 =
           let uu____22080 = singleton env prob in
           solve_and_commit env uu____22080
             (fun uu____22082  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22077)
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
      fun uu____22114  ->
        match uu____22114 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22153 =
                 let uu____22154 =
                   let uu____22159 =
                     let uu____22160 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22161 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22160 uu____22161 in
                   let uu____22162 = FStar_TypeChecker_Env.get_range env in
                   (uu____22159, uu____22162) in
                 FStar_Errors.Error uu____22154 in
               FStar_Exn.raise uu____22153) in
            let equiv1 v1 v' =
              let uu____22170 =
                let uu____22175 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22176 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22175, uu____22176) in
              match uu____22170 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22195 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22225 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22225 with
                      | FStar_Syntax_Syntax.U_unif uu____22232 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22261  ->
                                    match uu____22261 with
                                    | (u,v') ->
                                        let uu____22270 = equiv1 v1 v' in
                                        if uu____22270
                                        then
                                          let uu____22273 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22273 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22289 -> [])) in
            let uu____22294 =
              let wl =
                let uu___189_22298 = empty_worklist env in
                {
                  attempting = (uu___189_22298.attempting);
                  wl_deferred = (uu___189_22298.wl_deferred);
                  ctr = (uu___189_22298.ctr);
                  defer_ok = false;
                  smt_ok = (uu___189_22298.smt_ok);
                  tcenv = (uu___189_22298.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22316  ->
                      match uu____22316 with
                      | (lb,v1) ->
                          let uu____22323 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22323 with
                           | USolved wl1 -> ()
                           | uu____22325 -> fail lb v1))) in
            let rec check_ineq uu____22333 =
              match uu____22333 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22342) -> true
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
                      uu____22365,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22367,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22378) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22385,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22393 -> false) in
            let uu____22398 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22413  ->
                      match uu____22413 with
                      | (u,v1) ->
                          let uu____22420 = check_ineq (u, v1) in
                          if uu____22420
                          then true
                          else
                            ((let uu____22423 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22423
                              then
                                let uu____22424 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22425 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22424
                                  uu____22425
                              else ());
                             false))) in
            if uu____22398
            then ()
            else
              ((let uu____22429 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22429
                then
                  ((let uu____22431 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22431);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22441 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22441))
                else ());
               (let uu____22451 =
                  let uu____22452 =
                    let uu____22457 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22457) in
                  FStar_Errors.Error uu____22452 in
                FStar_Exn.raise uu____22451))
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
      let fail uu____22509 =
        match uu____22509 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22523 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22523
       then
         let uu____22524 = wl_to_string wl in
         let uu____22525 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22524 uu____22525
       else ());
      (let g1 =
         let uu____22540 = solve_and_commit env wl fail in
         match uu____22540 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___190_22553 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___190_22553.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___190_22553.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___190_22553.FStar_TypeChecker_Env.implicits)
             }
         | uu____22558 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___191_22562 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___191_22562.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___191_22562.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___191_22562.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22585 = FStar_ST.op_Bang last_proof_ns in
    match uu____22585 with
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
            let uu___192_22676 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___192_22676.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___192_22676.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___192_22676.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22677 =
            let uu____22678 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22678 in
          if uu____22677
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22686 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22686
                   then
                     let uu____22687 = FStar_TypeChecker_Env.get_range env in
                     let uu____22688 =
                       let uu____22689 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22689 in
                     FStar_Errors.diag uu____22687 uu____22688
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22692 = check_trivial vc1 in
                   match uu____22692 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22699 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22699
                           then
                             let uu____22700 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22701 =
                               let uu____22702 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22702 in
                             FStar_Errors.diag uu____22700 uu____22701
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22707 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22707
                           then
                             let uu____22708 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22709 =
                               let uu____22710 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22710 in
                             FStar_Errors.diag uu____22708 uu____22709
                           else ());
                          (let vcs =
                             let uu____22721 = FStar_Options.use_tactics () in
                             if uu____22721
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____22731 =
                                  let uu____22738 = FStar_Options.peek () in
                                  (env, vc2, uu____22738) in
                                [uu____22731]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____22772  ->
                                   match uu____22772 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____22783 = check_trivial goal1 in
                                       (match uu____22783 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____22785 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____22785
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____22792 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____22792
                                              then
                                                let uu____22793 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____22794 =
                                                  let uu____22795 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____22796 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____22795 uu____22796 in
                                                FStar_Errors.diag uu____22793
                                                  uu____22794
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
      let uu____22808 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22808 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22814 =
            let uu____22815 =
              let uu____22820 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22820) in
            FStar_Errors.Error uu____22815 in
          FStar_Exn.raise uu____22814
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22829 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22829 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits':
  Prims.bool ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun forcelax  ->
    fun g  ->
      let unresolved u =
        let uu____22847 = FStar_Syntax_Unionfind.find u in
        match uu____22847 with
        | FStar_Pervasives_Native.None  -> true
        | uu____22850 -> false in
      let rec until_fixpoint acc implicits =
        let uu____22868 = acc in
        match uu____22868 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____22954 = hd1 in
                 (match uu____22954 with
                  | (uu____22967,env,u,tm,k,r) ->
                      let uu____22973 = unresolved u in
                      if uu____22973
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____23004 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____23004
                          then
                            let uu____23005 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____23006 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____23007 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____23005 uu____23006 uu____23007
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___193_23010 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___193_23010.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___193_23010.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___193_23010.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___193_23010.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___193_23010.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___193_23010.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___193_23010.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___193_23010.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___193_23010.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___193_23010.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___193_23010.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___193_23010.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___193_23010.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___193_23010.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___193_23010.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___193_23010.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___193_23010.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___193_23010.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___193_23010.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___193_23010.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___193_23010.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___193_23010.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___193_23010.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___193_23010.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___193_23010.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___193_23010.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___193_23010.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___193_23010.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___193_23010.FStar_TypeChecker_Env.identifier_info)
                              }
                            else env1 in
                          let uu____23012 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___194_23020 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___194_23020.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___194_23020.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___194_23020.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___194_23020.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___194_23020.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___194_23020.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___194_23020.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___194_23020.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___194_23020.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___194_23020.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___194_23020.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___194_23020.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___194_23020.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___194_23020.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___194_23020.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___194_23020.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___194_23020.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___194_23020.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___194_23020.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___194_23020.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___194_23020.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___194_23020.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___194_23020.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___194_23020.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___194_23020.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___194_23020.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___194_23020.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___194_23020.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___194_23020.FStar_TypeChecker_Env.identifier_info)
                               }) tm1 in
                          match uu____23012 with
                          | (uu____23021,uu____23022,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___195_23025 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___195_23025.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___195_23025.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___195_23025.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____23028 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____23034  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____23028 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___196_23062 = g in
      let uu____23063 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___196_23062.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___196_23062.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___196_23062.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____23063
      }
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' false g
let resolve_implicits_lax:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' true g
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____23121 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23121 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23134 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23134
      | (reason,uu____23136,uu____23137,e,t,r)::uu____23141 ->
          let uu____23168 =
            let uu____23169 =
              let uu____23174 =
                let uu____23175 = FStar_Syntax_Print.term_to_string t in
                let uu____23176 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23175 uu____23176 in
              (uu____23174, r) in
            FStar_Errors.Error uu____23169 in
          FStar_Exn.raise uu____23168
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___197_23185 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___197_23185.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___197_23185.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___197_23185.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23214 = try_teq false env t1 t2 in
        match uu____23214 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23218 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23218 with
             | FStar_Pervasives_Native.Some uu____23223 -> true
             | FStar_Pervasives_Native.None  -> false)