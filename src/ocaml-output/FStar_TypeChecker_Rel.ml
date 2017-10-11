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
            let uu___157_128 = g1 in
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
                (uu___157_128.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___157_128.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___157_128.FStar_TypeChecker_Env.implicits)
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
          let uu___158_142 = g in
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
              (uu___158_142.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___158_142.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___158_142.FStar_TypeChecker_Env.implicits)
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
          let uu___159_187 = g in
          let uu____188 =
            let uu____189 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____189 in
          {
            FStar_TypeChecker_Env.guard_f = uu____188;
            FStar_TypeChecker_Env.deferred =
              (uu___159_187.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___159_187.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___159_187.FStar_TypeChecker_Env.implicits)
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
            let uu___160_329 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___160_329.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___160_329.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___160_329.FStar_TypeChecker_Env.implicits)
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
            let uu___161_367 = g in
            let uu____368 =
              let uu____369 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____369 in
            {
              FStar_TypeChecker_Env.guard_f = uu____368;
              FStar_TypeChecker_Env.deferred =
                (uu___161_367.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___161_367.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___161_367.FStar_TypeChecker_Env.implicits)
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
  fun uu___129_827  ->
    match uu___129_827 with
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
    fun uu___130_927  ->
      match uu___130_927 with
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
    fun uu___131_962  ->
      match uu___131_962 with
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
        let uu___162_1091 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___162_1091.wl_deferred);
          ctr = (uu___162_1091.ctr);
          defer_ok = (uu___162_1091.defer_ok);
          smt_ok;
          tcenv = (uu___162_1091.tcenv)
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
      let uu___163_1127 = empty_worklist env in
      let uu____1128 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1128;
        wl_deferred = (uu___163_1127.wl_deferred);
        ctr = (uu___163_1127.ctr);
        defer_ok = false;
        smt_ok = (uu___163_1127.smt_ok);
        tcenv = (uu___163_1127.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___164_1145 = wl in
        {
          attempting = (uu___164_1145.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___164_1145.ctr);
          defer_ok = (uu___164_1145.defer_ok);
          smt_ok = (uu___164_1145.smt_ok);
          tcenv = (uu___164_1145.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___165_1164 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___165_1164.wl_deferred);
        ctr = (uu___165_1164.ctr);
        defer_ok = (uu___165_1164.defer_ok);
        smt_ok = (uu___165_1164.smt_ok);
        tcenv = (uu___165_1164.tcenv)
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
  fun uu___132_1184  ->
    match uu___132_1184 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1191 'Auu____1192 .
    ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem ->
      ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___166_1209 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___166_1209.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___166_1209.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___166_1209.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___166_1209.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___166_1209.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___166_1209.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___166_1209.FStar_TypeChecker_Common.rank)
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
  fun uu___133_1242  ->
    match uu___133_1242 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___134_1268  ->
      match uu___134_1268 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___135_1272  ->
    match uu___135_1272 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___136_1286  ->
    match uu___136_1286 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___137_1302  ->
    match uu___137_1302 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___138_1318  ->
    match uu___138_1318 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___139_1336  ->
    match uu___139_1336 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___140_1354  ->
    match uu___140_1354 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___141_1368  ->
    match uu___141_1368 with
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
         (fun uu___142_1775  ->
            match uu___142_1775 with
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
        (fun uu___143_1811  ->
           match uu___143_1811 with
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
        (fun uu___144_1848  ->
           match uu___144_1848 with
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
                    let uu___167_1949 = x in
                    let uu____1950 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___167_1949.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___167_1949.FStar_Syntax_Syntax.index);
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
          let t12 = FStar_Syntax_Util.unmeta t11 in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2113 =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t12 in
                 match uu____2113 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2130;
                     FStar_Syntax_Syntax.vars = uu____2131;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2157 =
                       let uu____2158 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2159 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2158 uu____2159 in
                     failwith uu____2157)
          | FStar_Syntax_Syntax.Tm_uinst uu____2174 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t12 in
                 let uu____2211 =
                   let uu____2212 = FStar_Syntax_Subst.compress t1' in
                   uu____2212.FStar_Syntax_Syntax.n in
                 match uu____2211 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2229 -> aux true t1'
                 | uu____2236 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2251 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t12 in
                 let uu____2282 =
                   let uu____2283 = FStar_Syntax_Subst.compress t1' in
                   uu____2283.FStar_Syntax_Syntax.n in
                 match uu____2282 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2300 -> aux true t1'
                 | uu____2307 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2322 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t12 in
                 let uu____2367 =
                   let uu____2368 = FStar_Syntax_Subst.compress t1' in
                   uu____2368.FStar_Syntax_Syntax.n in
                 match uu____2367 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2385 -> aux true t1'
                 | uu____2392 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2407 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2422 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2437 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2452 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2467 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2494 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2525 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2556 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2583 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2620 ->
              let uu____2627 =
                let uu____2628 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2629 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2628 uu____2629 in
              failwith uu____2627
          | FStar_Syntax_Syntax.Tm_ascribed uu____2644 ->
              let uu____2671 =
                let uu____2672 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2673 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2672 uu____2673 in
              failwith uu____2671
          | FStar_Syntax_Syntax.Tm_delayed uu____2688 ->
              let uu____2713 =
                let uu____2714 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2715 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2714 uu____2715 in
              failwith uu____2713
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2730 =
                let uu____2731 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2732 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2731 uu____2732 in
              failwith uu____2730 in
        let uu____2747 = whnf env t1 in aux false uu____2747
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2756 =
        let uu____2771 = empty_worklist env in
        base_and_refinement env uu____2771 t in
      FStar_All.pipe_right uu____2756 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2806 = FStar_Syntax_Syntax.null_bv t in
    (uu____2806, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2815 .
    FStar_TypeChecker_Env.env ->
      'Auu____2815 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2832 = base_and_refinement env wl t in
        match uu____2832 with
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
  fun uu____2912  ->
    match uu____2912 with
    | (t_base,refopt) ->
        let uu____2939 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2939 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2974 =
      let uu____2977 =
        let uu____2980 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3003  ->
                  match uu____3003 with | (uu____3010,uu____3011,x) -> x)) in
        FStar_List.append wl.attempting uu____2980 in
      FStar_List.map (wl_prob_to_string wl) uu____2977 in
    FStar_All.pipe_right uu____2974 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3039 =
          let uu____3058 =
            let uu____3059 = FStar_Syntax_Subst.compress k in
            uu____3059.FStar_Syntax_Syntax.n in
          match uu____3058 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3124 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3124)
              else
                (let uu____3150 = FStar_Syntax_Util.abs_formals t in
                 match uu____3150 with
                 | (ys',t1,uu____3179) ->
                     let uu____3184 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3184))
          | uu____3225 ->
              let uu____3226 =
                let uu____3237 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3237) in
              ((ys, t), uu____3226) in
        match uu____3039 with
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
                 let uu____3316 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3316 c in
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
            let uu____3349 = p_guard prob in
            match uu____3349 with
            | (uu____3354,uv) ->
                ((let uu____3357 =
                    let uu____3358 = FStar_Syntax_Subst.compress uv in
                    uu____3358.FStar_Syntax_Syntax.n in
                  match uu____3357 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3390 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3390
                        then
                          let uu____3391 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3392 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3393 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3391
                            uu____3392 uu____3393
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3395 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___168_3398 = wl in
                  {
                    attempting = (uu___168_3398.attempting);
                    wl_deferred = (uu___168_3398.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___168_3398.defer_ok);
                    smt_ok = (uu___168_3398.smt_ok);
                    tcenv = (uu___168_3398.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3416 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3416
         then
           let uu____3417 = FStar_Util.string_of_int pid in
           let uu____3418 =
             let uu____3419 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3419 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3417 uu____3418
         else ());
        commit sol;
        (let uu___169_3426 = wl in
         {
           attempting = (uu___169_3426.attempting);
           wl_deferred = (uu___169_3426.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___169_3426.defer_ok);
           smt_ok = (uu___169_3426.smt_ok);
           tcenv = (uu___169_3426.tcenv)
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
            | (uu____3468,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3480 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3480 in
          (let uu____3486 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3486
           then
             let uu____3487 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3488 =
               let uu____3489 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3489 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3487 uu____3488
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
        let uu____3524 =
          let uu____3531 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3531 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3524
          (FStar_Util.for_some
             (fun uu____3567  ->
                match uu____3567 with
                | (uv,uu____3573) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3586 'Auu____3587 .
    'Auu____3587 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3586)
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
            let uu____3619 = occurs wl uk t in Prims.op_Negation uu____3619 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3626 =
                 let uu____3627 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3628 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3627 uu____3628 in
               FStar_Pervasives_Native.Some uu____3626) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3645 'Auu____3646 .
    'Auu____3646 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3645)
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
            let uu____3700 = occurs_check env wl uk t in
            match uu____3700 with
            | (occurs_ok,msg) ->
                let uu____3731 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3731, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3758 'Auu____3759 .
    (FStar_Syntax_Syntax.bv,'Auu____3759) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3758) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3758) FStar_Pervasives_Native.tuple2
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
      let uu____3843 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3897  ->
                fun uu____3898  ->
                  match (uu____3897, uu____3898) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3979 =
                        let uu____3980 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3980 in
                      if uu____3979
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4005 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4005
                         then
                           let uu____4018 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4018)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3843 with | (isect,uu____4059) -> FStar_List.rev isect
let binders_eq:
  'Auu____4088 'Auu____4089 .
    (FStar_Syntax_Syntax.bv,'Auu____4089) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4088) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4144  ->
              fun uu____4145  ->
                match (uu____4144, uu____4145) with
                | ((a,uu____4163),(b,uu____4165)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4184 'Auu____4185 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4185) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4184)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4184)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4236 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4250  ->
                      match uu____4250 with
                      | (b,uu____4256) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4236
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4272 -> FStar_Pervasives_Native.None
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
            let uu____4347 = pat_var_opt env seen hd1 in
            (match uu____4347 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4361 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4361
                   then
                     let uu____4362 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4362
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4381 =
      let uu____4382 = FStar_Syntax_Subst.compress t in
      uu____4382.FStar_Syntax_Syntax.n in
    match uu____4381 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4385 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4402;
           FStar_Syntax_Syntax.pos = uu____4403;
           FStar_Syntax_Syntax.vars = uu____4404;_},uu____4405)
        -> true
    | uu____4442 -> false
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
           FStar_Syntax_Syntax.pos = uu____4567;
           FStar_Syntax_Syntax.vars = uu____4568;_},args)
        -> (t, uv, k, args)
    | uu____4636 -> failwith "Not a flex-uvar"
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
      let uu____4715 = destruct_flex_t t in
      match uu____4715 with
      | (t1,uv,k,args) ->
          let uu____4830 = pat_vars env [] args in
          (match uu____4830 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4928 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5010 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5047 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5052 -> false
let head_match: match_result -> match_result =
  fun uu___145_5056  ->
    match uu___145_5056 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5071 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5082 ->
          let uu____5083 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5083 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5094 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5115 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5124 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5151 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5152 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5153 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5170 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5183 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5207) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5213,uu____5214) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5256) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5277;
             FStar_Syntax_Syntax.index = uu____5278;
             FStar_Syntax_Syntax.sort = t2;_},uu____5280)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5287 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5288 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5289 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5302 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5320 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5320
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
            let uu____5344 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5344
            then FullMatch
            else
              (let uu____5346 =
                 let uu____5355 =
                   let uu____5358 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5358 in
                 let uu____5359 =
                   let uu____5362 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5362 in
                 (uu____5355, uu____5359) in
               MisMatch uu____5346)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5368),FStar_Syntax_Syntax.Tm_uinst (g,uu____5370)) ->
            let uu____5379 = head_matches env f g in
            FStar_All.pipe_right uu____5379 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5388),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5390)) ->
            let uu____5439 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5439
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5446),FStar_Syntax_Syntax.Tm_refine (y,uu____5448)) ->
            let uu____5457 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5457 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5459),uu____5460) ->
            let uu____5465 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5465 head_match
        | (uu____5466,FStar_Syntax_Syntax.Tm_refine (x,uu____5468)) ->
            let uu____5473 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5473 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5474,FStar_Syntax_Syntax.Tm_type
           uu____5475) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5476,FStar_Syntax_Syntax.Tm_arrow uu____5477) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5503),FStar_Syntax_Syntax.Tm_app (head',uu____5505))
            ->
            let uu____5546 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5546 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5548),uu____5549) ->
            let uu____5570 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5570 head_match
        | (uu____5571,FStar_Syntax_Syntax.Tm_app (head1,uu____5573)) ->
            let uu____5594 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5594 head_match
        | uu____5595 ->
            let uu____5600 =
              let uu____5609 = delta_depth_of_term env t11 in
              let uu____5612 = delta_depth_of_term env t21 in
              (uu____5609, uu____5612) in
            MisMatch uu____5600
let head_matches_delta:
  'Auu____5629 .
    FStar_TypeChecker_Env.env ->
      'Auu____5629 ->
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
            let uu____5662 = FStar_Syntax_Util.head_and_args t in
            match uu____5662 with
            | (head1,uu____5680) ->
                let uu____5701 =
                  let uu____5702 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5702.FStar_Syntax_Syntax.n in
                (match uu____5701 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5708 =
                       let uu____5709 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5709 FStar_Option.isSome in
                     if uu____5708
                     then
                       let uu____5728 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5728
                         (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                     else FStar_Pervasives_Native.None
                 | uu____5732 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5835)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5853 =
                     let uu____5862 = maybe_inline t11 in
                     let uu____5865 = maybe_inline t21 in
                     (uu____5862, uu____5865) in
                   match uu____5853 with
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
                (uu____5902,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5920 =
                     let uu____5929 = maybe_inline t11 in
                     let uu____5932 = maybe_inline t21 in
                     (uu____5929, uu____5932) in
                   match uu____5920 with
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
                let uu____5975 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5975 with
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
                let uu____5998 =
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
                (match uu____5998 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6022 -> fail r
            | uu____6031 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6065 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6103 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___146_6117  ->
    match uu___146_6117 with
    | T (t,uu____6119) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6137 = FStar_Syntax_Util.type_u () in
      match uu____6137 with
      | (t,uu____6143) ->
          let uu____6144 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6144
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6157 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6157 FStar_Pervasives_Native.fst
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
        let uu____6223 = head_matches env t1 t' in
        match uu____6223 with
        | MisMatch uu____6224 -> false
        | uu____6233 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6329,imp),T (t2,uu____6332)) -> (t2, imp)
                     | uu____6351 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6418  ->
                    match uu____6418 with
                    | (t2,uu____6432) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6475 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6475 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6550))::tcs2) ->
                       aux
                         (((let uu___170_6585 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___170_6585.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___170_6585.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6603 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___147_6656 =
                 match uu___147_6656 with
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
               let uu____6773 = decompose1 [] bs1 in
               (rebuild, matches, uu____6773))
      | uu____6822 ->
          let rebuild uu___148_6828 =
            match uu___148_6828 with
            | [] -> t1
            | uu____6831 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___149_6863  ->
    match uu___149_6863 with
    | T (t,uu____6865) -> t
    | uu____6874 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___150_6878  ->
    match uu___150_6878 with
    | T (t,uu____6880) -> FStar_Syntax_Syntax.as_arg t
    | uu____6889 -> failwith "Impossible"
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
              | (uu____7000,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7025 = new_uvar r scope1 k in
                  (match uu____7025 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7043 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7060 =
                         let uu____7061 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_48  ->
                              FStar_TypeChecker_Common.TProb _0_48)
                           uu____7061 in
                       ((T (gi_xs, mk_kind)), uu____7060))
              | (uu____7074,uu____7075,C uu____7076) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7223 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7240;
                         FStar_Syntax_Syntax.vars = uu____7241;_})
                        ->
                        let uu____7264 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7264 with
                         | (T (gi_xs,uu____7288),prob) ->
                             let uu____7298 =
                               let uu____7299 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_49  -> C _0_49)
                                 uu____7299 in
                             (uu____7298, [prob])
                         | uu____7302 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7317;
                         FStar_Syntax_Syntax.vars = uu____7318;_})
                        ->
                        let uu____7341 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7341 with
                         | (T (gi_xs,uu____7365),prob) ->
                             let uu____7375 =
                               let uu____7376 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____7376 in
                             (uu____7375, [prob])
                         | uu____7379 -> failwith "impossible")
                    | (uu____7390,uu____7391,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7393;
                         FStar_Syntax_Syntax.vars = uu____7394;_})
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
                        let uu____7525 =
                          let uu____7534 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7534 FStar_List.unzip in
                        (match uu____7525 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7588 =
                                 let uu____7589 =
                                   let uu____7592 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7592 un_T in
                                 let uu____7593 =
                                   let uu____7602 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7602
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7589;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7593;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7588 in
                             ((C gi_xs), sub_probs))
                    | uu____7611 ->
                        let uu____7624 = sub_prob scope1 args q in
                        (match uu____7624 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7223 with
                   | (tc,probs) ->
                       let uu____7655 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7718,uu____7719),T
                            (t,uu____7721)) ->
                             let b1 =
                               ((let uu___171_7758 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___171_7758.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___171_7758.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7759 =
                               let uu____7766 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7766 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7759)
                         | uu____7801 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7655 with
                        | (bopt,scope2,args1) ->
                            let uu____7885 = aux scope2 args1 qs2 in
                            (match uu____7885 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7922 =
                                         let uu____7925 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7925 in
                                       FStar_Syntax_Util.mk_conj_l uu____7922
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7948 =
                                         let uu____7951 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7952 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7951 :: uu____7952 in
                                       FStar_Syntax_Util.mk_conj_l uu____7948 in
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
  'Auu____8023 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8023)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8023)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___172_8044 = p in
      let uu____8049 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8050 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___172_8044.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8049;
        FStar_TypeChecker_Common.relation =
          (uu___172_8044.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8050;
        FStar_TypeChecker_Common.element =
          (uu___172_8044.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___172_8044.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___172_8044.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___172_8044.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___172_8044.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___172_8044.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8064 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8064
            (fun _0_51  -> FStar_TypeChecker_Common.TProb _0_51)
      | FStar_TypeChecker_Common.CProb uu____8073 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8095 = compress_prob wl pr in
        FStar_All.pipe_right uu____8095 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8105 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8105 with
           | (lh,uu____8125) ->
               let uu____8146 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8146 with
                | (rh,uu____8166) ->
                    let uu____8187 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8204,FStar_Syntax_Syntax.Tm_uvar uu____8205)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8242,uu____8243)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8264,FStar_Syntax_Syntax.Tm_uvar uu____8265)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8286,uu____8287)
                          ->
                          let uu____8304 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8304 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8367 ->
                                    let rank =
                                      let uu____8377 = is_top_level_prob prob in
                                      if uu____8377
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8379 =
                                      let uu___173_8384 = tp in
                                      let uu____8389 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___173_8384.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___173_8384.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___173_8384.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8389;
                                        FStar_TypeChecker_Common.element =
                                          (uu___173_8384.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___173_8384.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___173_8384.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___173_8384.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___173_8384.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___173_8384.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8379)))
                      | (uu____8404,FStar_Syntax_Syntax.Tm_uvar uu____8405)
                          ->
                          let uu____8422 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8422 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8485 ->
                                    let uu____8494 =
                                      let uu___174_8501 = tp in
                                      let uu____8506 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___174_8501.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8506;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___174_8501.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___174_8501.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___174_8501.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___174_8501.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___174_8501.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___174_8501.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___174_8501.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___174_8501.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8494)))
                      | (uu____8527,uu____8528) -> (rigid_rigid, tp) in
                    (match uu____8187 with
                     | (rank,tp1) ->
                         let uu____8547 =
                           FStar_All.pipe_right
                             (let uu___175_8553 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___175_8553.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___175_8553.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___175_8553.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___175_8553.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___175_8553.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___175_8553.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___175_8553.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___175_8553.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___175_8553.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_52  ->
                                FStar_TypeChecker_Common.TProb _0_52) in
                         (rank, uu____8547))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8563 =
            FStar_All.pipe_right
              (let uu___176_8569 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___176_8569.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___176_8569.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___176_8569.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___176_8569.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___176_8569.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___176_8569.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___176_8569.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___176_8569.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___176_8569.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_53  -> FStar_TypeChecker_Common.CProb _0_53) in
          (rigid_rigid, uu____8563)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8625 probs =
      match uu____8625 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8678 = rank wl hd1 in
               (match uu____8678 with
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
    match projectee with | UDeferred _0 -> true | uu____8788 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8802 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8816 -> false
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
                        let uu____8861 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8861 with
                        | (k,uu____8867) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8877 -> false)))
            | uu____8878 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8929 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8929 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8932 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8942 =
                     let uu____8943 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8944 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8943
                       uu____8944 in
                   UFailed uu____8942)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8964 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8964 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8986 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8986 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8989 ->
                let uu____8994 =
                  let uu____8995 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8996 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8995
                    uu____8996 msg in
                UFailed uu____8994 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8997,uu____8998) ->
              let uu____8999 =
                let uu____9000 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9001 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9000 uu____9001 in
              failwith uu____8999
          | (FStar_Syntax_Syntax.U_unknown ,uu____9002) ->
              let uu____9003 =
                let uu____9004 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9005 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9004 uu____9005 in
              failwith uu____9003
          | (uu____9006,FStar_Syntax_Syntax.U_bvar uu____9007) ->
              let uu____9008 =
                let uu____9009 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9010 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9009 uu____9010 in
              failwith uu____9008
          | (uu____9011,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9012 =
                let uu____9013 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9014 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9013 uu____9014 in
              failwith uu____9012
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9038 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9038
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9060 = occurs_univ v1 u3 in
              if uu____9060
              then
                let uu____9061 =
                  let uu____9062 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9063 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9062 uu____9063 in
                try_umax_components u11 u21 uu____9061
              else
                (let uu____9065 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9065)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9085 = occurs_univ v1 u3 in
              if uu____9085
              then
                let uu____9086 =
                  let uu____9087 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9088 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9087 uu____9088 in
                try_umax_components u11 u21 uu____9086
              else
                (let uu____9090 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9090)
          | (FStar_Syntax_Syntax.U_max uu____9099,uu____9100) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9106 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9106
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9108,FStar_Syntax_Syntax.U_max uu____9109) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9115 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9115
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9117,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9118,FStar_Syntax_Syntax.U_name
             uu____9119) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9120) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9121) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9122,FStar_Syntax_Syntax.U_succ
             uu____9123) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9124,FStar_Syntax_Syntax.U_zero
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
      let uu____9218 = bc1 in
      match uu____9218 with
      | (bs1,mk_cod1) ->
          let uu____9259 = bc2 in
          (match uu____9259 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9329 = FStar_Util.first_N n1 bs in
                 match uu____9329 with
                 | (bs3,rest) ->
                     let uu____9354 = mk_cod rest in (bs3, uu____9354) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9383 =
                   let uu____9390 = mk_cod1 [] in (bs1, uu____9390) in
                 let uu____9393 =
                   let uu____9400 = mk_cod2 [] in (bs2, uu____9400) in
                 (uu____9383, uu____9393)
               else
                 if l1 > l2
                 then
                   (let uu____9442 = curry l2 bs1 mk_cod1 in
                    let uu____9455 =
                      let uu____9462 = mk_cod2 [] in (bs2, uu____9462) in
                    (uu____9442, uu____9455))
                 else
                   (let uu____9478 =
                      let uu____9485 = mk_cod1 [] in (bs1, uu____9485) in
                    let uu____9488 = curry l1 bs2 mk_cod2 in
                    (uu____9478, uu____9488)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9609 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9609
       then
         let uu____9610 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9610
       else ());
      (let uu____9612 = next_prob probs in
       match uu____9612 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___177_9633 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___177_9633.wl_deferred);
               ctr = (uu___177_9633.ctr);
               defer_ok = (uu___177_9633.defer_ok);
               smt_ok = (uu___177_9633.smt_ok);
               tcenv = (uu___177_9633.tcenv)
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
                  let uu____9644 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9644 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9649 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9649 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9654,uu____9655) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9672 ->
                let uu____9681 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9740  ->
                          match uu____9740 with
                          | (c,uu____9748,uu____9749) -> c < probs.ctr)) in
                (match uu____9681 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9790 =
                            FStar_List.map
                              (fun uu____9805  ->
                                 match uu____9805 with
                                 | (uu____9816,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9790
                      | uu____9819 ->
                          let uu____9828 =
                            let uu___178_9829 = probs in
                            let uu____9830 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9851  ->
                                      match uu____9851 with
                                      | (uu____9858,uu____9859,y) -> y)) in
                            {
                              attempting = uu____9830;
                              wl_deferred = rest;
                              ctr = (uu___178_9829.ctr);
                              defer_ok = (uu___178_9829.defer_ok);
                              smt_ok = (uu___178_9829.smt_ok);
                              tcenv = (uu___178_9829.tcenv)
                            } in
                          solve env uu____9828))))
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
            let uu____9866 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9866 with
            | USolved wl1 ->
                let uu____9868 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9868
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
                  let uu____9914 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9914 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9917 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9929;
                  FStar_Syntax_Syntax.vars = uu____9930;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9933;
                  FStar_Syntax_Syntax.vars = uu____9934;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9948,uu____9949) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9956,FStar_Syntax_Syntax.Tm_uinst uu____9957) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9964 -> USolved wl
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
            ((let uu____9974 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9974
              then
                let uu____9975 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9975 msg
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
        (let uu____9984 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9984
         then
           let uu____9985 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9985
         else ());
        (let uu____9987 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9987 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10049 = head_matches_delta env () t1 t2 in
               match uu____10049 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10090 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10139 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10154 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10155 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10154, uu____10155)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10160 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10161 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10160, uu____10161) in
                        (match uu____10139 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10187 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_54  ->
                                    FStar_TypeChecker_Common.TProb _0_54)
                                 uu____10187 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10218 =
                                    let uu____10227 =
                                      let uu____10230 =
                                        let uu____10233 =
                                          let uu____10234 =
                                            let uu____10241 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10241) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10234 in
                                        FStar_Syntax_Syntax.mk uu____10233 in
                                      uu____10230
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10249 =
                                      let uu____10252 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10252] in
                                    (uu____10227, uu____10249) in
                                  FStar_Pervasives_Native.Some uu____10218
                              | (uu____10265,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10267)) ->
                                  let uu____10272 =
                                    let uu____10279 =
                                      let uu____10282 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10282] in
                                    (t11, uu____10279) in
                                  FStar_Pervasives_Native.Some uu____10272
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10292),uu____10293) ->
                                  let uu____10298 =
                                    let uu____10305 =
                                      let uu____10308 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10308] in
                                    (t21, uu____10305) in
                                  FStar_Pervasives_Native.Some uu____10298
                              | uu____10317 ->
                                  let uu____10322 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10322 with
                                   | (head1,uu____10346) ->
                                       let uu____10367 =
                                         let uu____10368 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10368.FStar_Syntax_Syntax.n in
                                       (match uu____10367 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10379;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10381;_}
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
                                        | uu____10388 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10401) ->
                  let uu____10426 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___151_10452  ->
                            match uu___151_10452 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10459 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10459 with
                                      | (u',uu____10475) ->
                                          let uu____10496 =
                                            let uu____10497 = whnf env u' in
                                            uu____10497.FStar_Syntax_Syntax.n in
                                          (match uu____10496 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10501) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10526 -> false))
                                 | uu____10527 -> false)
                            | uu____10530 -> false)) in
                  (match uu____10426 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10564 tps =
                         match uu____10564 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10612 =
                                    let uu____10621 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10621 in
                                  (match uu____10612 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10656 -> FStar_Pervasives_Native.None) in
                       let uu____10665 =
                         let uu____10674 =
                           let uu____10681 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10681, []) in
                         make_lower_bound uu____10674 lower_bounds in
                       (match uu____10665 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10693 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10693
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
                            ((let uu____10713 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10713
                              then
                                let wl' =
                                  let uu___179_10715 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___179_10715.wl_deferred);
                                    ctr = (uu___179_10715.ctr);
                                    defer_ok = (uu___179_10715.defer_ok);
                                    smt_ok = (uu___179_10715.smt_ok);
                                    tcenv = (uu___179_10715.tcenv)
                                  } in
                                let uu____10716 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10716
                              else ());
                             (let uu____10718 =
                                solve_t env eq_prob
                                  (let uu___180_10720 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___180_10720.wl_deferred);
                                     ctr = (uu___180_10720.ctr);
                                     defer_ok = (uu___180_10720.defer_ok);
                                     smt_ok = (uu___180_10720.smt_ok);
                                     tcenv = (uu___180_10720.tcenv)
                                   }) in
                              match uu____10718 with
                              | Success uu____10723 ->
                                  let wl1 =
                                    let uu___181_10725 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___181_10725.wl_deferred);
                                      ctr = (uu___181_10725.ctr);
                                      defer_ok = (uu___181_10725.defer_ok);
                                      smt_ok = (uu___181_10725.smt_ok);
                                      tcenv = (uu___181_10725.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10727 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10732 -> FStar_Pervasives_Native.None))))
              | uu____10733 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10742 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10742
         then
           let uu____10743 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10743
         else ());
        (let uu____10745 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10745 with
         | (u,args) ->
             let uu____10784 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10784 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10825 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10825 with
                    | (h1,args1) ->
                        let uu____10866 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10866 with
                         | (h2,uu____10886) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10913 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10913
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10931 =
                                          let uu____10934 =
                                            let uu____10935 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_55  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_55) uu____10935 in
                                          [uu____10934] in
                                        FStar_Pervasives_Native.Some
                                          uu____10931))
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
                                       (let uu____10968 =
                                          let uu____10971 =
                                            let uu____10972 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____10972 in
                                          [uu____10971] in
                                        FStar_Pervasives_Native.Some
                                          uu____10968))
                                  else FStar_Pervasives_Native.None
                              | uu____10986 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11076 =
                               let uu____11085 =
                                 let uu____11088 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11088 in
                               (uu____11085, m1) in
                             FStar_Pervasives_Native.Some uu____11076)
                    | (uu____11101,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11103)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11151),uu____11152) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11199 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11252) ->
                       let uu____11277 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___152_11303  ->
                                 match uu___152_11303 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11310 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11310 with
                                           | (u',uu____11326) ->
                                               let uu____11347 =
                                                 let uu____11348 =
                                                   whnf env u' in
                                                 uu____11348.FStar_Syntax_Syntax.n in
                                               (match uu____11347 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11352) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11377 -> false))
                                      | uu____11378 -> false)
                                 | uu____11381 -> false)) in
                       (match uu____11277 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11419 tps =
                              match uu____11419 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11481 =
                                         let uu____11492 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11492 in
                                       (match uu____11481 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11543 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11554 =
                              let uu____11565 =
                                let uu____11574 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11574, []) in
                              make_upper_bound uu____11565 upper_bounds in
                            (match uu____11554 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11588 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11588
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
                                 ((let uu____11614 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11614
                                   then
                                     let wl' =
                                       let uu___182_11616 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___182_11616.wl_deferred);
                                         ctr = (uu___182_11616.ctr);
                                         defer_ok = (uu___182_11616.defer_ok);
                                         smt_ok = (uu___182_11616.smt_ok);
                                         tcenv = (uu___182_11616.tcenv)
                                       } in
                                     let uu____11617 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11617
                                   else ());
                                  (let uu____11619 =
                                     solve_t env eq_prob
                                       (let uu___183_11621 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___183_11621.wl_deferred);
                                          ctr = (uu___183_11621.ctr);
                                          defer_ok =
                                            (uu___183_11621.defer_ok);
                                          smt_ok = (uu___183_11621.smt_ok);
                                          tcenv = (uu___183_11621.tcenv)
                                        }) in
                                   match uu____11619 with
                                   | Success uu____11624 ->
                                       let wl1 =
                                         let uu___184_11626 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___184_11626.wl_deferred);
                                           ctr = (uu___184_11626.ctr);
                                           defer_ok =
                                             (uu___184_11626.defer_ok);
                                           smt_ok = (uu___184_11626.smt_ok);
                                           tcenv = (uu___184_11626.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11628 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11633 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11634 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11725 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11725
                      then
                        let uu____11726 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11726
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___185_11780 = hd1 in
                      let uu____11781 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___185_11780.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___185_11780.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11781
                      } in
                    let hd21 =
                      let uu___186_11785 = hd2 in
                      let uu____11786 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___186_11785.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___186_11785.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11786
                      } in
                    let prob =
                      let uu____11790 =
                        let uu____11795 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11795 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_57  -> FStar_TypeChecker_Common.TProb _0_57)
                        uu____11790 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11806 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11806 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11810 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11810 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11840 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11845 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11840 uu____11845 in
                         ((let uu____11855 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11855
                           then
                             let uu____11856 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11857 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11856 uu____11857
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11880 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11890 = aux scope env [] bs1 bs2 in
              match uu____11890 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11914 = compress_tprob wl problem in
        solve_t' env uu____11914 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11947 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11947 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11978,uu____11979) ->
                   let rec may_relate head3 =
                     let uu____12004 =
                       let uu____12005 = FStar_Syntax_Subst.compress head3 in
                       uu____12005.FStar_Syntax_Syntax.n in
                     match uu____12004 with
                     | FStar_Syntax_Syntax.Tm_name uu____12008 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12009 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12034,uu____12035) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12077) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12083) ->
                         may_relate t
                     | uu____12088 -> false in
                   let uu____12089 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12089
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
                                let uu____12106 =
                                  let uu____12107 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12107 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12106 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12109 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12109
                   else
                     (let uu____12111 =
                        let uu____12112 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12113 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12112 uu____12113 in
                      giveup env1 uu____12111 orig)
               | (uu____12114,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___187_12128 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___187_12128.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___187_12128.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___187_12128.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___187_12128.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___187_12128.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___187_12128.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___187_12128.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___187_12128.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12129,FStar_Pervasives_Native.None ) ->
                   ((let uu____12141 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12141
                     then
                       let uu____12142 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12143 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12144 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12145 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12142
                         uu____12143 uu____12144 uu____12145
                     else ());
                    (let uu____12147 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12147 with
                     | (head11,args1) ->
                         let uu____12184 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12184 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12238 =
                                  let uu____12239 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12240 = args_to_string args1 in
                                  let uu____12241 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12242 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12239 uu____12240 uu____12241
                                    uu____12242 in
                                giveup env1 uu____12238 orig
                              else
                                (let uu____12244 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12250 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12250 = FStar_Syntax_Util.Equal) in
                                 if uu____12244
                                 then
                                   let uu____12251 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12251 with
                                   | USolved wl2 ->
                                       let uu____12253 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12253
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12257 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12257 with
                                    | (base1,refinement1) ->
                                        let uu____12294 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12294 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12375 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12375 with
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
                                                           (fun uu____12397 
                                                              ->
                                                              fun uu____12398
                                                                 ->
                                                                match 
                                                                  (uu____12397,
                                                                    uu____12398)
                                                                with
                                                                | ((a,uu____12416),
                                                                   (a',uu____12418))
                                                                    ->
                                                                    let uu____12427
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
                                                                    uu____12427)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12437 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12437 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12443 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___188_12491 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___188_12491.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12530 =
          match uu____12530 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12746  ->
                              match uu____12746 with
                              | (x,imp) ->
                                  let uu____12757 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12757, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12770 = FStar_Syntax_Util.type_u () in
                      match uu____12770 with
                      | (t1,uu____12776) ->
                          let uu____12777 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12777 in
                    let uu____12782 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12782 with
                     | (t',tm_u1) ->
                         let uu____12795 = destruct_flex_t t' in
                         (match uu____12795 with
                          | (uu____12832,u1,k1,uu____12835) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12894 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12894 in
                              let sol =
                                let uu____12898 =
                                  let uu____12907 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12907) in
                                TERM uu____12898 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13043 = pat_var_opt env pat_args hd1 in
                    (match uu____13043 with
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
                                    (fun uu____13106  ->
                                       match uu____13106 with
                                       | (x,uu____13112) ->
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
                            let uu____13127 =
                              let uu____13128 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____13128 in
                            if uu____13127
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____13140 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____13140 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____13155::uu____13156) ->
                    let uu____13187 =
                      let uu____13200 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13200 in
                    (match uu____13187 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13239 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13246::uu____13247,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13282 =
                let uu____13295 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13295 in
              (match uu____13282 with
               | (all_formals,res_t) ->
                   let uu____13320 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13320 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13354 = lhs in
          match uu____13354 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13364 ->
                    let uu____13365 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13365 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13394 = p in
          match uu____13394 with
          | (((u,k),xs,c),ps,(h,uu____13405,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13487 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13487 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13510 = h gs_xs in
                     let uu____13511 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59) in
                     FStar_Syntax_Util.abs xs1 uu____13510 uu____13511 in
                   ((let uu____13517 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13517
                     then
                       let uu____13518 =
                         let uu____13521 =
                           let uu____13522 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13522
                             (FStar_String.concat "\n\t") in
                         let uu____13527 =
                           let uu____13530 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13531 =
                             let uu____13534 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13535 =
                               let uu____13538 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13539 =
                                 let uu____13542 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13543 =
                                   let uu____13546 =
                                     let uu____13547 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13547
                                       (FStar_String.concat ", ") in
                                   let uu____13552 =
                                     let uu____13555 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13555] in
                                   uu____13546 :: uu____13552 in
                                 uu____13542 :: uu____13543 in
                               uu____13538 :: uu____13539 in
                             uu____13534 :: uu____13535 in
                           uu____13530 :: uu____13531 in
                         uu____13521 :: uu____13527 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13518
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___153_13576 =
          match uu___153_13576 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13608 = p in
          match uu____13608 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13699 = FStar_List.nth ps i in
              (match uu____13699 with
               | (pi,uu____13703) ->
                   let uu____13708 = FStar_List.nth xs i in
                   (match uu____13708 with
                    | (xi,uu____13720) ->
                        let rec gs k =
                          let uu____13733 =
                            let uu____13746 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13746 in
                          match uu____13733 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13821)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13834 = new_uvar r xs k_a in
                                    (match uu____13834 with
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
                                         let uu____13856 = aux subst2 tl1 in
                                         (match uu____13856 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13883 =
                                                let uu____13886 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13886 :: gi_xs' in
                                              let uu____13887 =
                                                let uu____13890 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13890 :: gi_ps' in
                                              (uu____13883, uu____13887))) in
                              aux [] bs in
                        let uu____13895 =
                          let uu____13896 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13896 in
                        if uu____13895
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13900 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13900 with
                           | (g_xs,uu____13912) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13923 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13924 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_60  ->
                                        FStar_Pervasives_Native.Some _0_60) in
                                 FStar_Syntax_Util.abs xs uu____13923
                                   uu____13924 in
                               let sub1 =
                                 let uu____13930 =
                                   let uu____13935 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13938 =
                                     let uu____13941 =
                                       FStar_List.map
                                         (fun uu____13956  ->
                                            match uu____13956 with
                                            | (uu____13965,uu____13966,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13941 in
                                   mk_problem (p_scope orig) orig uu____13935
                                     (p_rel orig) uu____13938
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____13930 in
                               ((let uu____13981 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13981
                                 then
                                   let uu____13982 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13983 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13982 uu____13983
                                 else ());
                                (let wl2 =
                                   let uu____13986 =
                                     let uu____13989 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13989 in
                                   solve_prob orig uu____13986
                                     [TERM (u, proj)] wl1 in
                                 let uu____13998 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____13998))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14029 = lhs in
          match uu____14029 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14065 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14065 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14098 =
                        let uu____14145 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14145) in
                      FStar_Pervasives_Native.Some uu____14098
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14289 =
                           let uu____14296 =
                             let uu____14297 = FStar_Syntax_Subst.compress k1 in
                             uu____14297.FStar_Syntax_Syntax.n in
                           (uu____14296, args) in
                         match uu____14289 with
                         | (uu____14308,[]) ->
                             let uu____14311 =
                               let uu____14322 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14322) in
                             FStar_Pervasives_Native.Some uu____14311
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14343,uu____14344) ->
                             let uu____14365 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14365 with
                              | (uv1,uv_args) ->
                                  let uu____14408 =
                                    let uu____14409 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14409.FStar_Syntax_Syntax.n in
                                  (match uu____14408 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14419) ->
                                       let uu____14444 =
                                         pat_vars env [] uv_args in
                                       (match uu____14444 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14471  ->
                                                      let uu____14472 =
                                                        let uu____14473 =
                                                          let uu____14474 =
                                                            let uu____14479 =
                                                              let uu____14480
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14480
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14479 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14474 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14473 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14472)) in
                                            let c1 =
                                              let uu____14490 =
                                                let uu____14491 =
                                                  let uu____14496 =
                                                    let uu____14497 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14497
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14496 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14491 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14490 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14510 =
                                                let uu____14513 =
                                                  let uu____14514 =
                                                    let uu____14517 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14517
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14514 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14513 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14510 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14535 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14540,uu____14541) ->
                             let uu____14560 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14560 with
                              | (uv1,uv_args) ->
                                  let uu____14603 =
                                    let uu____14604 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14604.FStar_Syntax_Syntax.n in
                                  (match uu____14603 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14614) ->
                                       let uu____14639 =
                                         pat_vars env [] uv_args in
                                       (match uu____14639 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14666  ->
                                                      let uu____14667 =
                                                        let uu____14668 =
                                                          let uu____14669 =
                                                            let uu____14674 =
                                                              let uu____14675
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14675
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14674 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14669 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14668 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14667)) in
                                            let c1 =
                                              let uu____14685 =
                                                let uu____14686 =
                                                  let uu____14691 =
                                                    let uu____14692 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14692
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14691 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14686 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14685 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14705 =
                                                let uu____14708 =
                                                  let uu____14709 =
                                                    let uu____14712 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14712
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14709 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14708 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14705 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14730 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14737) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14778 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14778
                                 (fun _0_63  ->
                                    FStar_Pervasives_Native.Some _0_63)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14814 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14814 with
                                  | (args1,rest) ->
                                      let uu____14843 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14843 with
                                       | (xs2,c2) ->
                                           let uu____14856 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14856
                                             (fun uu____14880  ->
                                                match uu____14880 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14920 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14920 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14988 =
                                        let uu____14993 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14993 in
                                      FStar_All.pipe_right uu____14988
                                        (fun _0_64  ->
                                           FStar_Pervasives_Native.Some _0_64))
                         | uu____15008 ->
                             let uu____15015 =
                               let uu____15016 =
                                 let uu____15021 =
                                   let uu____15022 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____15023 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____15024 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____15022 uu____15023 uu____15024 in
                                 (uu____15021, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____15016 in
                             FStar_Exn.raise uu____15015 in
                       let uu____15031 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15031
                         (fun uu____15086  ->
                            match uu____15086 with
                            | (xs1,c1) ->
                                let uu____15135 =
                                  let uu____15176 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15176) in
                                FStar_Pervasives_Native.Some uu____15135)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15297 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15313 = project orig env wl1 i st in
                     match uu____15313 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15327) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15342 = imitate orig env wl1 st in
                  match uu____15342 with
                  | Failed uu____15347 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15378 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15378 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15403 =
                      let uu____15404 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15404 wl2 in
                    (match uu____15403 with
                     | Failed uu____15405 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15423 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15423 with
                | (hd1,uu____15439) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15460 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15473 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15474 -> true
                     | uu____15491 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15495 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15495
                         then true
                         else
                           ((let uu____15498 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15498
                             then
                               let uu____15499 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____15499
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15519 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15519 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15532 =
                            let uu____15533 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15533 in
                          giveup_or_defer1 orig uu____15532
                        else
                          (let uu____15535 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15535
                           then
                             let uu____15536 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15536
                              then
                                let uu____15537 = subterms args_lhs in
                                imitate' orig env wl1 uu____15537
                              else
                                ((let uu____15542 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15542
                                  then
                                    let uu____15543 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15544 = names_to_string fvs1 in
                                    let uu____15545 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15543 uu____15544 uu____15545
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
                               (let uu____15549 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15549
                                then
                                  ((let uu____15551 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15551
                                    then
                                      let uu____15552 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15553 = names_to_string fvs1 in
                                      let uu____15554 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15552 uu____15553 uu____15554
                                    else ());
                                   (let uu____15556 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15556))
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
                     (let uu____15567 =
                        let uu____15568 = FStar_Syntax_Free.names t1 in
                        check_head uu____15568 t2 in
                      if uu____15567
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15579 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15579
                          then
                            let uu____15580 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15581 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15580 uu____15581
                          else ());
                         (let uu____15589 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15589))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15666 uu____15667 r =
               match (uu____15666, uu____15667) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15865 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15865
                   then
                     let uu____15866 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15866
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15890 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15890
                       then
                         let uu____15891 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15892 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15893 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15894 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15895 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15891 uu____15892 uu____15893 uu____15894
                           uu____15895
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15955 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15955 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15969 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15969 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16023 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16023 in
                                  let uu____16026 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16026 k3)
                           else
                             (let uu____16030 =
                                let uu____16031 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16032 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16033 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16031 uu____16032 uu____16033 in
                              failwith uu____16030) in
                       let uu____16034 =
                         let uu____16041 =
                           let uu____16054 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16054 in
                         match uu____16041 with
                         | (bs,k1') ->
                             let uu____16079 =
                               let uu____16092 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16092 in
                             (match uu____16079 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16120 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      uu____16120 in
                                  let uu____16129 =
                                    let uu____16134 =
                                      let uu____16135 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16135.FStar_Syntax_Syntax.n in
                                    let uu____16138 =
                                      let uu____16139 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16139.FStar_Syntax_Syntax.n in
                                    (uu____16134, uu____16138) in
                                  (match uu____16129 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16148,uu____16149) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16152,FStar_Syntax_Syntax.Tm_type
                                      uu____16153) -> (k2'_ys, [sub_prob])
                                   | uu____16156 ->
                                       let uu____16161 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16161 with
                                        | (t,uu____16173) ->
                                            let uu____16174 = new_uvar r zs t in
                                            (match uu____16174 with
                                             | (k_zs,uu____16186) ->
                                                 let kprob =
                                                   let uu____16188 =
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
                                                          _0_66) uu____16188 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16034 with
                       | (k_u',sub_probs) ->
                           let uu____16205 =
                             let uu____16216 =
                               let uu____16217 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16217 in
                             let uu____16226 =
                               let uu____16229 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16229 in
                             let uu____16232 =
                               let uu____16235 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16235 in
                             (uu____16216, uu____16226, uu____16232) in
                           (match uu____16205 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16254 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16254 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16273 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16273
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16277 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16277 with
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
             let solve_one_pat uu____16330 uu____16331 =
               match (uu____16330, uu____16331) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16449 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16449
                     then
                       let uu____16450 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16451 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16450 uu____16451
                     else ());
                    (let uu____16453 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16453
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16472  ->
                              fun uu____16473  ->
                                match (uu____16472, uu____16473) with
                                | ((a,uu____16491),(t21,uu____16493)) ->
                                    let uu____16502 =
                                      let uu____16507 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16507
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16502
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67))
                           xs args2 in
                       let guard =
                         let uu____16513 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16513 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16528 = occurs_check env wl (u1, k1) t21 in
                        match uu____16528 with
                        | (occurs_ok,uu____16536) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16544 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16544
                            then
                              let sol =
                                let uu____16546 =
                                  let uu____16555 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16555) in
                                TERM uu____16546 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16562 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16562
                               then
                                 let uu____16563 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16563 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16587,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16613 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16613
                                       then
                                         let uu____16614 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16614
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16621 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16623 = lhs in
             match uu____16623 with
             | (t1,u1,k1,args1) ->
                 let uu____16628 = rhs in
                 (match uu____16628 with
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
                       | uu____16668 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16678 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16678 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16696) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16703 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16703
                                    then
                                      let uu____16704 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16704
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16711 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16713 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16713
        then
          let uu____16714 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16714
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16718 = FStar_Util.physical_equality t1 t2 in
           if uu____16718
           then
             let uu____16719 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16719
           else
             ((let uu____16722 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16722
               then
                 let uu____16723 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16723
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16726,uu____16727) ->
                   let uu____16754 =
                     let uu___189_16755 = problem in
                     let uu____16756 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___189_16755.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16756;
                       FStar_TypeChecker_Common.relation =
                         (uu___189_16755.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___189_16755.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___189_16755.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___189_16755.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___189_16755.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___189_16755.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___189_16755.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___189_16755.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16754 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16757,uu____16758) ->
                   let uu____16765 =
                     let uu___189_16766 = problem in
                     let uu____16767 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___189_16766.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16767;
                       FStar_TypeChecker_Common.relation =
                         (uu___189_16766.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___189_16766.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___189_16766.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___189_16766.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___189_16766.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___189_16766.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___189_16766.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___189_16766.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16765 wl
               | (uu____16768,FStar_Syntax_Syntax.Tm_ascribed uu____16769) ->
                   let uu____16796 =
                     let uu___190_16797 = problem in
                     let uu____16798 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___190_16797.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___190_16797.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___190_16797.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16798;
                       FStar_TypeChecker_Common.element =
                         (uu___190_16797.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___190_16797.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___190_16797.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___190_16797.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___190_16797.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___190_16797.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16796 wl
               | (uu____16799,FStar_Syntax_Syntax.Tm_meta uu____16800) ->
                   let uu____16807 =
                     let uu___190_16808 = problem in
                     let uu____16809 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___190_16808.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___190_16808.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___190_16808.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16809;
                       FStar_TypeChecker_Common.element =
                         (uu___190_16808.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___190_16808.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___190_16808.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___190_16808.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___190_16808.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___190_16808.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16807 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16810,uu____16811) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16812,FStar_Syntax_Syntax.Tm_bvar uu____16813) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___154_16868 =
                     match uu___154_16868 with
                     | [] -> c
                     | bs ->
                         let uu____16890 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16890 in
                   let uu____16899 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16899 with
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
                                   let uu____17041 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17041
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17043 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.CProb _0_68)
                                   uu____17043))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___155_17119 =
                     match uu___155_17119 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17153 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17153 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17289 =
                                   let uu____17294 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17295 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17294
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17295 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17289))
               | (FStar_Syntax_Syntax.Tm_abs uu____17300,uu____17301) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17326 -> true
                     | uu____17343 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17377 =
                     let uu____17394 = maybe_eta t1 in
                     let uu____17401 = maybe_eta t2 in
                     (uu____17394, uu____17401) in
                   (match uu____17377 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___191_17443 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___191_17443.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___191_17443.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___191_17443.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___191_17443.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___191_17443.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___191_17443.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___191_17443.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___191_17443.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17466 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17466
                        then
                          let uu____17467 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17467 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17495 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17495
                        then
                          let uu____17496 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17496 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17504 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17521,FStar_Syntax_Syntax.Tm_abs uu____17522) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17547 -> true
                     | uu____17564 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17598 =
                     let uu____17615 = maybe_eta t1 in
                     let uu____17622 = maybe_eta t2 in
                     (uu____17615, uu____17622) in
                   (match uu____17598 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___191_17664 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___191_17664.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___191_17664.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___191_17664.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___191_17664.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___191_17664.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___191_17664.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___191_17664.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___191_17664.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17687 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17687
                        then
                          let uu____17688 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17688 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17716 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17716
                        then
                          let uu____17717 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17717 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17725 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17742,FStar_Syntax_Syntax.Tm_refine uu____17743) ->
                   let uu____17756 = as_refinement env wl t1 in
                   (match uu____17756 with
                    | (x1,phi1) ->
                        let uu____17763 = as_refinement env wl t2 in
                        (match uu____17763 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17771 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_70  ->
                                    FStar_TypeChecker_Common.TProb _0_70)
                                 uu____17771 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17809 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17809
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17813 =
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
                                 let uu____17819 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17819 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17828 =
                                   let uu____17833 =
                                     let uu____17834 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____17834 :: (p_scope orig) in
                                   mk_problem uu____17833 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.TProb _0_71)
                                   uu____17828 in
                               let uu____17839 =
                                 solve env1
                                   (let uu___192_17841 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___192_17841.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___192_17841.smt_ok);
                                      tcenv = (uu___192_17841.tcenv)
                                    }) in
                               (match uu____17839 with
                                | Failed uu____17848 -> fallback ()
                                | Success uu____17853 ->
                                    let guard =
                                      let uu____17857 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17862 =
                                        let uu____17863 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17863
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17857
                                        uu____17862 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___193_17872 = wl1 in
                                      {
                                        attempting =
                                          (uu___193_17872.attempting);
                                        wl_deferred =
                                          (uu___193_17872.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___193_17872.defer_ok);
                                        smt_ok = (uu___193_17872.smt_ok);
                                        tcenv = (uu___193_17872.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17874,FStar_Syntax_Syntax.Tm_uvar uu____17875) ->
                   let uu____17908 = destruct_flex_t t1 in
                   let uu____17909 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17908 uu____17909
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17910;
                     FStar_Syntax_Syntax.pos = uu____17911;
                     FStar_Syntax_Syntax.vars = uu____17912;_},uu____17913),FStar_Syntax_Syntax.Tm_uvar
                  uu____17914) ->
                   let uu____17967 = destruct_flex_t t1 in
                   let uu____17968 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17967 uu____17968
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17969,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17970;
                     FStar_Syntax_Syntax.pos = uu____17971;
                     FStar_Syntax_Syntax.vars = uu____17972;_},uu____17973))
                   ->
                   let uu____18026 = destruct_flex_t t1 in
                   let uu____18027 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18026 uu____18027
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18028;
                     FStar_Syntax_Syntax.pos = uu____18029;
                     FStar_Syntax_Syntax.vars = uu____18030;_},uu____18031),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18032;
                     FStar_Syntax_Syntax.pos = uu____18033;
                     FStar_Syntax_Syntax.vars = uu____18034;_},uu____18035))
                   ->
                   let uu____18108 = destruct_flex_t t1 in
                   let uu____18109 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18108 uu____18109
               | (FStar_Syntax_Syntax.Tm_uvar uu____18110,uu____18111) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18128 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18128 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18135;
                     FStar_Syntax_Syntax.pos = uu____18136;
                     FStar_Syntax_Syntax.vars = uu____18137;_},uu____18138),uu____18139)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18176 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18176 t2 wl
               | (uu____18183,FStar_Syntax_Syntax.Tm_uvar uu____18184) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18201,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18202;
                     FStar_Syntax_Syntax.pos = uu____18203;
                     FStar_Syntax_Syntax.vars = uu____18204;_},uu____18205))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18242,FStar_Syntax_Syntax.Tm_type uu____18243) ->
                   solve_t' env
                     (let uu___194_18261 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___194_18261.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___194_18261.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___194_18261.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___194_18261.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___194_18261.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___194_18261.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___194_18261.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___194_18261.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___194_18261.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18262;
                     FStar_Syntax_Syntax.pos = uu____18263;
                     FStar_Syntax_Syntax.vars = uu____18264;_},uu____18265),FStar_Syntax_Syntax.Tm_type
                  uu____18266) ->
                   solve_t' env
                     (let uu___194_18304 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___194_18304.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___194_18304.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___194_18304.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___194_18304.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___194_18304.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___194_18304.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___194_18304.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___194_18304.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___194_18304.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18305,FStar_Syntax_Syntax.Tm_arrow uu____18306) ->
                   solve_t' env
                     (let uu___194_18336 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___194_18336.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___194_18336.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___194_18336.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___194_18336.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___194_18336.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___194_18336.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___194_18336.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___194_18336.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___194_18336.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18337;
                     FStar_Syntax_Syntax.pos = uu____18338;
                     FStar_Syntax_Syntax.vars = uu____18339;_},uu____18340),FStar_Syntax_Syntax.Tm_arrow
                  uu____18341) ->
                   solve_t' env
                     (let uu___194_18391 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___194_18391.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___194_18391.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___194_18391.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___194_18391.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___194_18391.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___194_18391.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___194_18391.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___194_18391.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___194_18391.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18392,uu____18393) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18412 =
                        let uu____18413 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18413 in
                      if uu____18412
                      then
                        let uu____18414 =
                          FStar_All.pipe_left
                            (fun _0_72  ->
                               FStar_TypeChecker_Common.TProb _0_72)
                            (let uu___195_18420 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___195_18420.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___195_18420.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___195_18420.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___195_18420.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___195_18420.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___195_18420.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___195_18420.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___195_18420.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___195_18420.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18421 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18414 uu____18421 t2
                          wl
                      else
                        (let uu____18429 = base_and_refinement env wl t2 in
                         match uu____18429 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18472 =
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      (let uu___196_18478 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___196_18478.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___196_18478.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___196_18478.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___196_18478.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___196_18478.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___196_18478.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___196_18478.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___196_18478.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___196_18478.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18479 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18472
                                    uu____18479 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___197_18499 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___197_18499.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___197_18499.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18502 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      uu____18502 in
                                  let guard =
                                    let uu____18514 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18514
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18522;
                     FStar_Syntax_Syntax.pos = uu____18523;
                     FStar_Syntax_Syntax.vars = uu____18524;_},uu____18525),uu____18526)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18565 =
                        let uu____18566 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18566 in
                      if uu____18565
                      then
                        let uu____18567 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___195_18573 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___195_18573.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___195_18573.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___195_18573.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___195_18573.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___195_18573.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___195_18573.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___195_18573.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___195_18573.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___195_18573.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18574 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18567 uu____18574 t2
                          wl
                      else
                        (let uu____18582 = base_and_refinement env wl t2 in
                         match uu____18582 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18625 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___196_18631 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___196_18631.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___196_18631.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___196_18631.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___196_18631.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___196_18631.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___196_18631.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___196_18631.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___196_18631.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___196_18631.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18632 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18625
                                    uu____18632 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___197_18652 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___197_18652.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___197_18652.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18655 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____18655 in
                                  let guard =
                                    let uu____18667 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18667
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18675,FStar_Syntax_Syntax.Tm_uvar uu____18676) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18694 = base_and_refinement env wl t1 in
                      match uu____18694 with
                      | (t_base,uu____18710) ->
                          solve_t env
                            (let uu___198_18732 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___198_18732.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___198_18732.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___198_18732.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___198_18732.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___198_18732.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___198_18732.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___198_18732.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___198_18732.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18735,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18736;
                     FStar_Syntax_Syntax.pos = uu____18737;
                     FStar_Syntax_Syntax.vars = uu____18738;_},uu____18739))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18777 = base_and_refinement env wl t1 in
                      match uu____18777 with
                      | (t_base,uu____18793) ->
                          solve_t env
                            (let uu___198_18815 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___198_18815.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___198_18815.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___198_18815.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___198_18815.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___198_18815.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___198_18815.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___198_18815.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___198_18815.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18818,uu____18819) ->
                   let t21 =
                     let uu____18829 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18829 in
                   solve_t env
                     (let uu___199_18853 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___199_18853.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___199_18853.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___199_18853.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___199_18853.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___199_18853.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___199_18853.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___199_18853.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___199_18853.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___199_18853.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18854,FStar_Syntax_Syntax.Tm_refine uu____18855) ->
                   let t11 =
                     let uu____18865 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18865 in
                   solve_t env
                     (let uu___200_18889 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___200_18889.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___200_18889.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___200_18889.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___200_18889.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___200_18889.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___200_18889.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___200_18889.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___200_18889.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___200_18889.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18892,uu____18893) ->
                   let head1 =
                     let uu____18919 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18919
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18963 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18963
                       FStar_Pervasives_Native.fst in
                   let uu____19004 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19004
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19019 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19019
                      then
                        let guard =
                          let uu____19031 =
                            let uu____19032 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19032 = FStar_Syntax_Util.Equal in
                          if uu____19031
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19036 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19036) in
                        let uu____19039 = solve_prob orig guard [] wl in
                        solve env uu____19039
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19042,uu____19043) ->
                   let head1 =
                     let uu____19053 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19053
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19097 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19097
                       FStar_Pervasives_Native.fst in
                   let uu____19138 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19138
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19153 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19153
                      then
                        let guard =
                          let uu____19165 =
                            let uu____19166 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19166 = FStar_Syntax_Util.Equal in
                          if uu____19165
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19170 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19170) in
                        let uu____19173 = solve_prob orig guard [] wl in
                        solve env uu____19173
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19176,uu____19177) ->
                   let head1 =
                     let uu____19181 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19181
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19225 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19225
                       FStar_Pervasives_Native.fst in
                   let uu____19266 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19266
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19281 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19281
                      then
                        let guard =
                          let uu____19293 =
                            let uu____19294 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19294 = FStar_Syntax_Util.Equal in
                          if uu____19293
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19298 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19298) in
                        let uu____19301 = solve_prob orig guard [] wl in
                        solve env uu____19301
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19304,uu____19305) ->
                   let head1 =
                     let uu____19309 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19309
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19353 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19353
                       FStar_Pervasives_Native.fst in
                   let uu____19394 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19394
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19409 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19409
                      then
                        let guard =
                          let uu____19421 =
                            let uu____19422 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19422 = FStar_Syntax_Util.Equal in
                          if uu____19421
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19426 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19426) in
                        let uu____19429 = solve_prob orig guard [] wl in
                        solve env uu____19429
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19432,uu____19433) ->
                   let head1 =
                     let uu____19437 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19437
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19481 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19481
                       FStar_Pervasives_Native.fst in
                   let uu____19522 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19522
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19537 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19537
                      then
                        let guard =
                          let uu____19549 =
                            let uu____19550 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19550 = FStar_Syntax_Util.Equal in
                          if uu____19549
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19554 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19554) in
                        let uu____19557 = solve_prob orig guard [] wl in
                        solve env uu____19557
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19560,uu____19561) ->
                   let head1 =
                     let uu____19579 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19579
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19623 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19623
                       FStar_Pervasives_Native.fst in
                   let uu____19664 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19664
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19679 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19679
                      then
                        let guard =
                          let uu____19691 =
                            let uu____19692 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19692 = FStar_Syntax_Util.Equal in
                          if uu____19691
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19696 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19696) in
                        let uu____19699 = solve_prob orig guard [] wl in
                        solve env uu____19699
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19702,FStar_Syntax_Syntax.Tm_match uu____19703) ->
                   let head1 =
                     let uu____19729 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19729
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19773 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19773
                       FStar_Pervasives_Native.fst in
                   let uu____19814 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19814
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19829 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19829
                      then
                        let guard =
                          let uu____19841 =
                            let uu____19842 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19842 = FStar_Syntax_Util.Equal in
                          if uu____19841
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19846 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19846) in
                        let uu____19849 = solve_prob orig guard [] wl in
                        solve env uu____19849
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19852,FStar_Syntax_Syntax.Tm_uinst uu____19853) ->
                   let head1 =
                     let uu____19863 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19863
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19907 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19907
                       FStar_Pervasives_Native.fst in
                   let uu____19948 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19948
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19963 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19963
                      then
                        let guard =
                          let uu____19975 =
                            let uu____19976 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19976 = FStar_Syntax_Util.Equal in
                          if uu____19975
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19980 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19980) in
                        let uu____19983 = solve_prob orig guard [] wl in
                        solve env uu____19983
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19986,FStar_Syntax_Syntax.Tm_name uu____19987) ->
                   let head1 =
                     let uu____19991 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19991
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20035 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20035
                       FStar_Pervasives_Native.fst in
                   let uu____20076 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20076
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20091 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20091
                      then
                        let guard =
                          let uu____20103 =
                            let uu____20104 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20104 = FStar_Syntax_Util.Equal in
                          if uu____20103
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20108 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20108) in
                        let uu____20111 = solve_prob orig guard [] wl in
                        solve env uu____20111
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20114,FStar_Syntax_Syntax.Tm_constant uu____20115) ->
                   let head1 =
                     let uu____20119 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20119
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20163 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20163
                       FStar_Pervasives_Native.fst in
                   let uu____20204 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20204
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20219 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20219
                      then
                        let guard =
                          let uu____20231 =
                            let uu____20232 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20232 = FStar_Syntax_Util.Equal in
                          if uu____20231
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20236 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20236) in
                        let uu____20239 = solve_prob orig guard [] wl in
                        solve env uu____20239
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20242,FStar_Syntax_Syntax.Tm_fvar uu____20243) ->
                   let head1 =
                     let uu____20247 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20247
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20291 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20291
                       FStar_Pervasives_Native.fst in
                   let uu____20332 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20332
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20347 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20347
                      then
                        let guard =
                          let uu____20359 =
                            let uu____20360 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20360 = FStar_Syntax_Util.Equal in
                          if uu____20359
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20364 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20364) in
                        let uu____20367 = solve_prob orig guard [] wl in
                        solve env uu____20367
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20370,FStar_Syntax_Syntax.Tm_app uu____20371) ->
                   let head1 =
                     let uu____20389 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20389
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20433 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20433
                       FStar_Pervasives_Native.fst in
                   let uu____20474 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20474
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20489 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20489
                      then
                        let guard =
                          let uu____20501 =
                            let uu____20502 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20502 = FStar_Syntax_Util.Equal in
                          if uu____20501
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20506 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_Pervasives_Native.Some _0_89)
                               uu____20506) in
                        let uu____20509 = solve_prob orig guard [] wl in
                        solve env uu____20509
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20512,uu____20513) ->
                   let uu____20526 =
                     let uu____20527 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20528 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20527
                       uu____20528 in
                   failwith uu____20526
               | (FStar_Syntax_Syntax.Tm_delayed uu____20529,uu____20530) ->
                   let uu____20555 =
                     let uu____20556 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20557 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20556
                       uu____20557 in
                   failwith uu____20555
               | (uu____20558,FStar_Syntax_Syntax.Tm_delayed uu____20559) ->
                   let uu____20584 =
                     let uu____20585 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20586 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20585
                       uu____20586 in
                   failwith uu____20584
               | (uu____20587,FStar_Syntax_Syntax.Tm_let uu____20588) ->
                   let uu____20601 =
                     let uu____20602 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20603 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20602
                       uu____20603 in
                   failwith uu____20601
               | uu____20604 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20640 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20640
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20642 =
               let uu____20643 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20644 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20643 uu____20644 in
             giveup env uu____20642 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20664  ->
                    fun uu____20665  ->
                      match (uu____20664, uu____20665) with
                      | ((a1,uu____20683),(a2,uu____20685)) ->
                          let uu____20694 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_90  ->
                               FStar_TypeChecker_Common.TProb _0_90)
                            uu____20694)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20704 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20704 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20728 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20735)::[] -> wp1
              | uu____20752 ->
                  let uu____20761 =
                    let uu____20762 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20762 in
                  failwith uu____20761 in
            let uu____20765 =
              let uu____20774 =
                let uu____20775 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20775 in
              [uu____20774] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20765;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20776 = lift_c1 () in solve_eq uu____20776 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___156_20782  ->
                       match uu___156_20782 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20783 -> false)) in
             let uu____20784 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20818)::uu____20819,(wp2,uu____20821)::uu____20822)
                   -> (wp1, wp2)
               | uu____20879 ->
                   let uu____20900 =
                     let uu____20901 =
                       let uu____20906 =
                         let uu____20907 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20908 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20907 uu____20908 in
                       (uu____20906, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20901 in
                   FStar_Exn.raise uu____20900 in
             match uu____20784 with
             | (wpc1,wpc2) ->
                 let uu____20927 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20927
                 then
                   let uu____20930 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20930 wl
                 else
                   (let uu____20934 =
                      let uu____20941 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20941 in
                    match uu____20934 with
                    | (c2_decl,qualifiers) ->
                        let uu____20962 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20962
                        then
                          let c1_repr =
                            let uu____20966 =
                              let uu____20967 =
                                let uu____20968 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20968 in
                              let uu____20969 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20967 uu____20969 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20966 in
                          let c2_repr =
                            let uu____20971 =
                              let uu____20972 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20973 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20972 uu____20973 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20971 in
                          let prob =
                            let uu____20975 =
                              let uu____20980 =
                                let uu____20981 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20982 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20981
                                  uu____20982 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20980 in
                            FStar_TypeChecker_Common.TProb uu____20975 in
                          let wl1 =
                            let uu____20984 =
                              let uu____20987 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20987 in
                            solve_prob orig uu____20984 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20996 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20996
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____20998 =
                                     let uu____21001 =
                                       let uu____21002 =
                                         let uu____21017 =
                                           let uu____21018 =
                                             let uu____21019 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____21019] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____21018 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21020 =
                                           let uu____21023 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21024 =
                                             let uu____21027 =
                                               let uu____21028 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21028 in
                                             [uu____21027] in
                                           uu____21023 :: uu____21024 in
                                         (uu____21017, uu____21020) in
                                       FStar_Syntax_Syntax.Tm_app uu____21002 in
                                     FStar_Syntax_Syntax.mk uu____21001 in
                                   uu____20998 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____21035 =
                                    let uu____21038 =
                                      let uu____21039 =
                                        let uu____21054 =
                                          let uu____21055 =
                                            let uu____21056 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____21056] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____21055 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21057 =
                                          let uu____21060 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21061 =
                                            let uu____21064 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21065 =
                                              let uu____21068 =
                                                let uu____21069 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21069 in
                                              [uu____21068] in
                                            uu____21064 :: uu____21065 in
                                          uu____21060 :: uu____21061 in
                                        (uu____21054, uu____21057) in
                                      FStar_Syntax_Syntax.Tm_app uu____21039 in
                                    FStar_Syntax_Syntax.mk uu____21038 in
                                  uu____21035 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21076 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_91  ->
                                  FStar_TypeChecker_Common.TProb _0_91)
                               uu____21076 in
                           let wl1 =
                             let uu____21086 =
                               let uu____21089 =
                                 let uu____21092 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21092 g in
                               FStar_All.pipe_left
                                 (fun _0_92  ->
                                    FStar_Pervasives_Native.Some _0_92)
                                 uu____21089 in
                             solve_prob orig uu____21086 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21105 = FStar_Util.physical_equality c1 c2 in
        if uu____21105
        then
          let uu____21106 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21106
        else
          ((let uu____21109 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21109
            then
              let uu____21110 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21111 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21110
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21111
            else ());
           (let uu____21113 =
              let uu____21118 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21119 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21118, uu____21119) in
            match uu____21113 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21123),FStar_Syntax_Syntax.Total
                    (t2,uu____21125)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21142 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21142 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21145,FStar_Syntax_Syntax.Total uu____21146) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21164),FStar_Syntax_Syntax.Total
                    (t2,uu____21166)) ->
                     let uu____21183 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21183 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21187),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21189)) ->
                     let uu____21206 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21206 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21210),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21212)) ->
                     let uu____21229 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21229 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21232,FStar_Syntax_Syntax.Comp uu____21233) ->
                     let uu____21242 =
                       let uu___201_21247 = problem in
                       let uu____21252 =
                         let uu____21253 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21253 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_21247.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21252;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_21247.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_21247.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_21247.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_21247.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___201_21247.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_21247.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_21247.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_21247.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21242 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21254,FStar_Syntax_Syntax.Comp uu____21255) ->
                     let uu____21264 =
                       let uu___201_21269 = problem in
                       let uu____21274 =
                         let uu____21275 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21275 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_21269.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21274;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_21269.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_21269.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_21269.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_21269.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___201_21269.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_21269.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_21269.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_21269.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21264 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21276,FStar_Syntax_Syntax.GTotal uu____21277) ->
                     let uu____21286 =
                       let uu___202_21291 = problem in
                       let uu____21296 =
                         let uu____21297 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21297 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_21291.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_21291.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_21291.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21296;
                         FStar_TypeChecker_Common.element =
                           (uu___202_21291.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_21291.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___202_21291.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_21291.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_21291.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_21291.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21286 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21298,FStar_Syntax_Syntax.Total uu____21299) ->
                     let uu____21308 =
                       let uu___202_21313 = problem in
                       let uu____21318 =
                         let uu____21319 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21319 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_21313.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_21313.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_21313.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21318;
                         FStar_TypeChecker_Common.element =
                           (uu___202_21313.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_21313.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___202_21313.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_21313.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_21313.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_21313.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21308 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21320,FStar_Syntax_Syntax.Comp uu____21321) ->
                     let uu____21322 =
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
                     if uu____21322
                     then
                       let uu____21323 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21323 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21329 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21339 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21340 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21339, uu____21340)) in
                          match uu____21329 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21347 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21347
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21349 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21349 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21352 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21354 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21354) in
                                if uu____21352
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
                                  (let uu____21357 =
                                     let uu____21358 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21359 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21358 uu____21359 in
                                   giveup env uu____21357 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21365 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21403  ->
              match uu____21403 with
              | (uu____21416,uu____21417,u,uu____21419,uu____21420,uu____21421)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21365 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21453 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21453 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21471 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21499  ->
                match uu____21499 with
                | (u1,u2) ->
                    let uu____21506 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21507 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21506 uu____21507)) in
      FStar_All.pipe_right uu____21471 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21526,[])) -> "{}"
      | uu____21551 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21568 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21568
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21571 =
              FStar_List.map
                (fun uu____21581  ->
                   match uu____21581 with
                   | (uu____21586,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21571 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21591 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21591 imps
let new_t_problem:
  'Auu____21606 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21606 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21606)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21640 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21640
                then
                  let uu____21641 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21642 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21641
                    (rel_to_string rel) uu____21642
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
            let uu____21670 =
              let uu____21673 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21673 in
            FStar_Syntax_Syntax.new_bv uu____21670 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21682 =
              let uu____21685 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_94  -> FStar_Pervasives_Native.Some _0_94)
                uu____21685 in
            let uu____21688 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21682 uu____21688 in
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
          let uu____21721 = FStar_Options.eager_inference () in
          if uu____21721
          then
            let uu___203_21722 = probs in
            {
              attempting = (uu___203_21722.attempting);
              wl_deferred = (uu___203_21722.wl_deferred);
              ctr = (uu___203_21722.ctr);
              defer_ok = false;
              smt_ok = (uu___203_21722.smt_ok);
              tcenv = (uu___203_21722.tcenv)
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
             (let uu____21734 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21734
              then
                let uu____21735 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21735
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
          ((let uu____21747 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21747
            then
              let uu____21748 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21748
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21752 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21752
             then
               let uu____21753 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21753
             else ());
            (let f2 =
               let uu____21756 =
                 let uu____21757 = FStar_Syntax_Util.unmeta f1 in
                 uu____21757.FStar_Syntax_Syntax.n in
               match uu____21756 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21761 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___204_21762 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___204_21762.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___204_21762.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___204_21762.FStar_TypeChecker_Env.implicits)
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
            let uu____21784 =
              let uu____21785 =
                let uu____21786 =
                  let uu____21787 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21787
                    (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21786;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21785 in
            FStar_All.pipe_left
              (fun _0_96  -> FStar_Pervasives_Native.Some _0_96) uu____21784
let with_guard_no_simp:
  'Auu____21818 .
    'Auu____21818 ->
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
            let uu____21838 =
              let uu____21839 =
                let uu____21840 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21840
                  (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21839;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21838
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
          (let uu____21882 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21882
           then
             let uu____21883 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21884 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21883
               uu____21884
           else ());
          (let prob =
             let uu____21887 =
               let uu____21892 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21892 in
             FStar_All.pipe_left
               (fun _0_98  -> FStar_TypeChecker_Common.TProb _0_98)
               uu____21887 in
           let g =
             let uu____21900 =
               let uu____21903 = singleton' env prob smt_ok in
               solve_and_commit env uu____21903
                 (fun uu____21905  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21900 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21926 = try_teq true env t1 t2 in
        match uu____21926 with
        | FStar_Pervasives_Native.None  ->
            let uu____21929 =
              let uu____21930 =
                let uu____21935 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21936 = FStar_TypeChecker_Env.get_range env in
                (uu____21935, uu____21936) in
              FStar_Errors.Error uu____21930 in
            FStar_Exn.raise uu____21929
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21939 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21939
              then
                let uu____21940 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21941 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21942 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21940
                  uu____21941 uu____21942
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
          (let uu____21963 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21963
           then
             let uu____21964 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21965 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21964
               uu____21965
           else ());
          (let uu____21967 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21967 with
           | (prob,x) ->
               let g =
                 let uu____21979 =
                   let uu____21982 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21982
                     (fun uu____21984  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21979 in
               ((let uu____21994 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____21994
                 then
                   let uu____21995 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____21996 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____21997 =
                     let uu____21998 = FStar_Util.must g in
                     guard_to_string env uu____21998 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____21995 uu____21996 uu____21997
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
          let uu____22030 = FStar_TypeChecker_Env.get_range env in
          let uu____22031 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____22030 uu____22031
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22047 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22047
         then
           let uu____22048 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22049 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22048
             uu____22049
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22054 =
             let uu____22059 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22059 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_99  -> FStar_TypeChecker_Common.CProb _0_99) uu____22054 in
         let uu____22064 =
           let uu____22067 = singleton env prob in
           solve_and_commit env uu____22067
             (fun uu____22069  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22064)
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
      fun uu____22101  ->
        match uu____22101 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22140 =
                 let uu____22141 =
                   let uu____22146 =
                     let uu____22147 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22148 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22147 uu____22148 in
                   let uu____22149 = FStar_TypeChecker_Env.get_range env in
                   (uu____22146, uu____22149) in
                 FStar_Errors.Error uu____22141 in
               FStar_Exn.raise uu____22140) in
            let equiv1 v1 v' =
              let uu____22157 =
                let uu____22162 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22163 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22162, uu____22163) in
              match uu____22157 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22182 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22212 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22212 with
                      | FStar_Syntax_Syntax.U_unif uu____22219 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22248  ->
                                    match uu____22248 with
                                    | (u,v') ->
                                        let uu____22257 = equiv1 v1 v' in
                                        if uu____22257
                                        then
                                          let uu____22260 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22260 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22276 -> [])) in
            let uu____22281 =
              let wl =
                let uu___205_22285 = empty_worklist env in
                {
                  attempting = (uu___205_22285.attempting);
                  wl_deferred = (uu___205_22285.wl_deferred);
                  ctr = (uu___205_22285.ctr);
                  defer_ok = false;
                  smt_ok = (uu___205_22285.smt_ok);
                  tcenv = (uu___205_22285.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22303  ->
                      match uu____22303 with
                      | (lb,v1) ->
                          let uu____22310 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22310 with
                           | USolved wl1 -> ()
                           | uu____22312 -> fail lb v1))) in
            let rec check_ineq uu____22320 =
              match uu____22320 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22329) -> true
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
                      uu____22352,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22354,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22365) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22372,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22380 -> false) in
            let uu____22385 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22400  ->
                      match uu____22400 with
                      | (u,v1) ->
                          let uu____22407 = check_ineq (u, v1) in
                          if uu____22407
                          then true
                          else
                            ((let uu____22410 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22410
                              then
                                let uu____22411 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22412 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22411
                                  uu____22412
                              else ());
                             false))) in
            if uu____22385
            then ()
            else
              ((let uu____22416 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22416
                then
                  ((let uu____22418 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22418);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22428 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22428))
                else ());
               (let uu____22438 =
                  let uu____22439 =
                    let uu____22444 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22444) in
                  FStar_Errors.Error uu____22439 in
                FStar_Exn.raise uu____22438))
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
      let fail uu____22496 =
        match uu____22496 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22510 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22510
       then
         let uu____22511 = wl_to_string wl in
         let uu____22512 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22511 uu____22512
       else ());
      (let g1 =
         let uu____22527 = solve_and_commit env wl fail in
         match uu____22527 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___206_22540 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___206_22540.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___206_22540.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___206_22540.FStar_TypeChecker_Env.implicits)
             }
         | uu____22545 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___207_22549 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___207_22549.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___207_22549.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___207_22549.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22572 = FStar_ST.op_Bang last_proof_ns in
    match uu____22572 with
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
            let uu___208_22759 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___208_22759.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___208_22759.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___208_22759.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22760 =
            let uu____22761 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22761 in
          if uu____22760
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22769 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22769
                   then
                     let uu____22770 = FStar_TypeChecker_Env.get_range env in
                     let uu____22771 =
                       let uu____22772 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22772 in
                     FStar_Errors.diag uu____22770 uu____22771
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22775 = check_trivial vc1 in
                   match uu____22775 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22782 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22782
                           then
                             let uu____22783 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22784 =
                               let uu____22785 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22785 in
                             FStar_Errors.diag uu____22783 uu____22784
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22790 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22790
                           then
                             let uu____22791 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22792 =
                               let uu____22793 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22793 in
                             FStar_Errors.diag uu____22791 uu____22792
                           else ());
                          (let vcs =
                             let uu____22804 = FStar_Options.use_tactics () in
                             if uu____22804
                             then
                               FStar_Options.with_saved_options
                                 (fun uu____22823  ->
                                    (let uu____22825 =
                                       FStar_Options.set_options
                                         FStar_Options.Set "--no_tactics" in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____22825);
                                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                      env vc2)
                             else
                               (let uu____22827 =
                                  let uu____22834 = FStar_Options.peek () in
                                  (env, vc2, uu____22834) in
                                [uu____22827]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____22868  ->
                                   match uu____22868 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____22879 = check_trivial goal1 in
                                       (match uu____22879 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____22881 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____22881
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____22888 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____22888
                                              then
                                                let uu____22889 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____22890 =
                                                  let uu____22891 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____22892 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____22891 uu____22892 in
                                                FStar_Errors.diag uu____22889
                                                  uu____22890
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
      let uu____22904 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22904 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22910 =
            let uu____22911 =
              let uu____22916 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22916) in
            FStar_Errors.Error uu____22911 in
          FStar_Exn.raise uu____22910
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22925 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22925 with
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
          let uu____22947 = FStar_Syntax_Unionfind.find u in
          match uu____22947 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22950 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22968 = acc in
          match uu____22968 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23054 = hd1 in
                   (match uu____23054 with
                    | (uu____23067,env,u,tm,k,r) ->
                        let uu____23073 = unresolved u in
                        if uu____23073
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____23104 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23104
                            then
                              let uu____23105 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23106 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23107 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23105 uu____23106 uu____23107
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___209_23110 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___209_23110.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___209_23110.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___209_23110.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___209_23110.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___209_23110.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___209_23110.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___209_23110.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___209_23110.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___209_23110.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___209_23110.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___209_23110.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___209_23110.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___209_23110.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___209_23110.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___209_23110.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___209_23110.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___209_23110.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___209_23110.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___209_23110.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___209_23110.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___209_23110.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___209_23110.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___209_23110.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___209_23110.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___209_23110.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___209_23110.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___209_23110.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___209_23110.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___209_23110.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___209_23110.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___209_23110.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___209_23110.FStar_TypeChecker_Env.dsenv)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____23113 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___210_23121 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___210_23121.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___210_23121.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___210_23121.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___210_23121.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___210_23121.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___210_23121.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___210_23121.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___210_23121.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___210_23121.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___210_23121.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___210_23121.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___210_23121.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___210_23121.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___210_23121.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___210_23121.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___210_23121.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___210_23121.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___210_23121.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___210_23121.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___210_23121.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___210_23121.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___210_23121.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___210_23121.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___210_23121.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___210_23121.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___210_23121.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___210_23121.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___210_23121.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___210_23121.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___210_23121.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___210_23121.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___210_23121.FStar_TypeChecker_Env.dsenv)
                                     }) tm1 in
                                match uu____23113 with
                                | (uu____23122,uu____23123,g1) -> g1
                              else
                                (let uu____23126 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___211_23134 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___211_23134.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___211_23134.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___211_23134.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___211_23134.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___211_23134.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___211_23134.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___211_23134.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___211_23134.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___211_23134.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___211_23134.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___211_23134.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___211_23134.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___211_23134.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___211_23134.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___211_23134.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___211_23134.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___211_23134.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___211_23134.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___211_23134.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___211_23134.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___211_23134.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___211_23134.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___211_23134.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___211_23134.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___211_23134.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___211_23134.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___211_23134.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___211_23134.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___211_23134.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___211_23134.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___211_23134.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___211_23134.FStar_TypeChecker_Env.dsenv)
                                      }) tm1 in
                                 match uu____23126 with
                                 | (uu____23135,uu____23136,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___212_23139 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___212_23139.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___212_23139.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___212_23139.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23142 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23148  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23142 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___213_23176 = g in
        let uu____23177 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___213_23176.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___213_23176.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___213_23176.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23177
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
        let uu____23235 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23235 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23248 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23248
      | (reason,uu____23250,uu____23251,e,t,r)::uu____23255 ->
          let uu____23282 =
            let uu____23283 =
              let uu____23288 =
                let uu____23289 = FStar_Syntax_Print.term_to_string t in
                let uu____23290 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23289 uu____23290 in
              (uu____23288, r) in
            FStar_Errors.Error uu____23283 in
          FStar_Exn.raise uu____23282
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___214_23299 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___214_23299.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___214_23299.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___214_23299.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23328 = try_teq false env t1 t2 in
        match uu____23328 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23332 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23332 with
             | FStar_Pervasives_Native.Some uu____23337 -> true
             | FStar_Pervasives_Native.None  -> false)