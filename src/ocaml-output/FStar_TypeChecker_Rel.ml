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
            let uu___165_128 = g1 in
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
                (uu___165_128.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___165_128.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___165_128.FStar_TypeChecker_Env.implicits)
            } in
          FStar_Pervasives_Native.Some uu____127
let guard_unbound_vars:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          FStar_Util.new_set FStar_Syntax_Syntax.order_bv
      | FStar_TypeChecker_Common.NonTrivial f ->
          FStar_TypeChecker_Env.unbound_vars env f
let check_guard:
  Prims.string ->
    FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit
  =
  fun msg  ->
    fun env  ->
      fun g  ->
        let s = guard_unbound_vars env g in
        let uu____161 = FStar_Util.set_is_empty s in
        if uu____161
        then ()
        else
          (let uu____163 =
             let uu____164 =
               let uu____165 =
                 let uu____166 =
                   let uu____169 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____169
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____166
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format2 "Guard has free variables (%s): %s" msg
                 uu____165 in
             FStar_Errors.Err uu____164 in
           FStar_Exn.raise uu____163)
let check_term:
  Prims.string ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun msg  ->
    fun env  ->
      fun t  ->
        let s = FStar_TypeChecker_Env.unbound_vars env t in
        let uu____193 = FStar_Util.set_is_empty s in
        if uu____193
        then ()
        else
          (let uu____195 =
             let uu____196 =
               let uu____197 = FStar_Syntax_Print.term_to_string t in
               let uu____198 =
                 let uu____199 =
                   let uu____202 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____202
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____199
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format3 "Term <%s> has free variables (%s): %s"
                 uu____197 msg uu____198 in
             FStar_Errors.Err uu____196 in
           FStar_Exn.raise uu____195)
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___166_220 = g in
          let uu____221 =
            let uu____222 =
              let uu____223 =
                let uu____226 =
                  let uu____227 =
                    let uu____242 =
                      let uu____245 = FStar_Syntax_Syntax.as_arg e in
                      [uu____245] in
                    (f, uu____242) in
                  FStar_Syntax_Syntax.Tm_app uu____227 in
                FStar_Syntax_Syntax.mk uu____226 in
              uu____223 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_42  -> FStar_TypeChecker_Common.NonTrivial _0_42)
              uu____222 in
          {
            FStar_TypeChecker_Env.guard_f = uu____221;
            FStar_TypeChecker_Env.deferred =
              (uu___166_220.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___166_220.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___166_220.FStar_TypeChecker_Env.implicits)
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
          let uu___167_265 = g in
          let uu____266 =
            let uu____267 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____267 in
          {
            FStar_TypeChecker_Env.guard_f = uu____266;
            FStar_TypeChecker_Env.deferred =
              (uu___167_265.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___167_265.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___167_265.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____272 -> failwith "impossible"
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
          let uu____285 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____285
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____290 =
      let uu____291 = FStar_Syntax_Util.unmeta t in
      uu____291.FStar_Syntax_Syntax.n in
    match uu____290 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____295 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____331 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____331;
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
                       let uu____405 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____405
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___168_407 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___168_407.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___168_407.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___168_407.FStar_TypeChecker_Env.implicits)
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
               let uu____429 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____429
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
            let uu___169_445 = g in
            let uu____446 =
              let uu____447 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____447 in
            {
              FStar_TypeChecker_Env.guard_f = uu____446;
              FStar_TypeChecker_Env.deferred =
                (uu___169_445.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___169_445.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___169_445.FStar_TypeChecker_Env.implicits)
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
        | uu____480 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____505 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____505 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____513 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____513, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____544 = FStar_Syntax_Util.type_u () in
        match uu____544 with
        | (t_type,u) ->
            let uu____551 =
              let uu____556 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____556 t_type in
            (match uu____551 with
             | (tt,uu____558) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2[@@deriving show]
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
    match projectee with | UNIV _0 -> true | uu____634 -> false
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
    match projectee with | Success _0 -> true | uu____828 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____846 -> false
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
    match projectee with | COVARIANT  -> true | uu____871 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____876 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____881 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___137_905  ->
    match uu___137_905 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____912 =
        let uu____913 = FStar_Syntax_Subst.compress t in
        uu____913.FStar_Syntax_Syntax.n in
      match uu____912 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____942 = FStar_Syntax_Print.uvar_to_string u in
          let uu____943 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____942 uu____943
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____946;
             FStar_Syntax_Syntax.vars = uu____947;_},args)
          ->
          let uu____993 = FStar_Syntax_Print.uvar_to_string u in
          let uu____994 = FStar_Syntax_Print.term_to_string ty in
          let uu____995 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____993 uu____994 uu____995
      | uu____996 -> "--" in
    let uu____997 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____997 detail
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___138_1005  ->
      match uu___138_1005 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1011 =
            let uu____1014 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____1015 =
              let uu____1018 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____1019 =
                let uu____1022 =
                  let uu____1025 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____1025] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1022 in
              uu____1018 :: uu____1019 in
            uu____1014 :: uu____1015 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1011
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1031 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____1032 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____1031
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1032
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___139_1040  ->
      match uu___139_1040 with
      | UNIV (u,t) ->
          let x =
            let uu____1044 = FStar_Options.hide_uvar_nums () in
            if uu____1044
            then "?"
            else
              (let uu____1046 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____1046 FStar_Util.string_of_int) in
          let uu____1047 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____1047
      | TERM ((u,uu____1049),t) ->
          let x =
            let uu____1056 = FStar_Options.hide_uvar_nums () in
            if uu____1056
            then "?"
            else
              (let uu____1058 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____1058 FStar_Util.string_of_int) in
          let uu____1059 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____1059
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____1072 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____1072 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____1085 =
      let uu____1088 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1088
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1085 (FStar_String.concat ", ")
let args_to_string:
  'Auu____1101 .
    (FStar_Syntax_Syntax.term,'Auu____1101) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1118 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1136  ->
              match uu____1136 with
              | (x,uu____1142) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1118 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1149 =
      let uu____1150 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1150 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1149;
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
        let uu___170_1169 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___170_1169.wl_deferred);
          ctr = (uu___170_1169.ctr);
          defer_ok = (uu___170_1169.defer_ok);
          smt_ok;
          tcenv = (uu___170_1169.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1184 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1184,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___171_1205 = empty_worklist env in
      let uu____1206 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1206;
        wl_deferred = (uu___171_1205.wl_deferred);
        ctr = (uu___171_1205.ctr);
        defer_ok = false;
        smt_ok = (uu___171_1205.smt_ok);
        tcenv = (uu___171_1205.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___172_1223 = wl in
        {
          attempting = (uu___172_1223.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___172_1223.ctr);
          defer_ok = (uu___172_1223.defer_ok);
          smt_ok = (uu___172_1223.smt_ok);
          tcenv = (uu___172_1223.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___173_1242 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___173_1242.wl_deferred);
        ctr = (uu___173_1242.ctr);
        defer_ok = (uu___173_1242.defer_ok);
        smt_ok = (uu___173_1242.smt_ok);
        tcenv = (uu___173_1242.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1256 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1256
         then
           let uu____1257 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1257
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___140_1262  ->
    match uu___140_1262 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1269 'Auu____1270 .
    ('Auu____1270,'Auu____1269) FStar_TypeChecker_Common.problem ->
      ('Auu____1270,'Auu____1269) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___174_1287 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___174_1287.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___174_1287.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___174_1287.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___174_1287.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___174_1287.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___174_1287.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___174_1287.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1298 'Auu____1299 .
    ('Auu____1299,'Auu____1298) FStar_TypeChecker_Common.problem ->
      ('Auu____1299,'Auu____1298) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___141_1320  ->
    match uu___141_1320 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___142_1346  ->
      match uu___142_1346 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___143_1350  ->
    match uu___143_1350 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___144_1364  ->
    match uu___144_1364 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___145_1380  ->
    match uu___145_1380 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___146_1396  ->
    match uu___146_1396 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___147_1414  ->
    match uu___147_1414 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___148_1432  ->
    match uu___148_1432 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___149_1446  ->
    match uu___149_1446 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.TProb _0_45) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_46  -> FStar_TypeChecker_Common.CProb _0_46) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1469 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1469 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1482  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1583 'Auu____1584 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1584 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1584 ->
              'Auu____1583 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1584,'Auu____1583)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1621 = next_pid () in
                let uu____1622 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1621;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1622;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1645 'Auu____1646 .
    FStar_TypeChecker_Env.env ->
      'Auu____1646 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1646 ->
            'Auu____1645 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1646,'Auu____1645)
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
                let uu____1684 = next_pid () in
                let uu____1685 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1684;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1685;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1706 'Auu____1707 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1707 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1707 ->
            'Auu____1706 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1707,'Auu____1706) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1740 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1740;
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
  'Auu____1751 .
    worklist ->
      ('Auu____1751,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1804 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1804
        then
          let uu____1805 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1806 = prob_to_string env d in
          let uu____1807 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1805 uu____1806 uu____1807 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1813 -> failwith "impossible" in
           let uu____1814 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1828 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1829 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1828, uu____1829)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1835 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1836 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1835, uu____1836) in
           match uu____1814 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___150_1853  ->
            match uu___150_1853 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1865 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1867),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___151_1889  ->
           match uu___151_1889 with
           | UNIV uu____1892 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1898),t) ->
               let uu____1904 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1904
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
        (fun uu___152_1926  ->
           match uu___152_1926 with
           | UNIV (u',t) ->
               let uu____1931 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1931
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1935 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1944 =
        let uu____1945 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1945 in
      FStar_Syntax_Subst.compress uu____1944
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1954 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1954
let norm_arg:
  'Auu____1961 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1961) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1961)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1982 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1982, (FStar_Pervasives_Native.snd t))
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
           (fun uu____2015  ->
              match uu____2015 with
              | (x,imp) ->
                  let uu____2026 =
                    let uu___175_2027 = x in
                    let uu____2028 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___175_2027.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___175_2027.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2028
                    } in
                  (uu____2026, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2045 = aux u3 in FStar_Syntax_Syntax.U_succ uu____2045
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2049 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____2049
        | uu____2052 -> u2 in
      let uu____2053 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2053
let normalize_refinement:
  'Auu____2064 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2064 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement:
  'Auu____2089 .
    FStar_TypeChecker_Env.env ->
      'Auu____2089 ->
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
                (let uu____2191 =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 match uu____2191 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2208;
                     FStar_Syntax_Syntax.vars = uu____2209;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2235 =
                       let uu____2236 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2237 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2236 uu____2237 in
                     failwith uu____2235)
          | FStar_Syntax_Syntax.Tm_uinst uu____2252 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 let uu____2289 =
                   let uu____2290 = FStar_Syntax_Subst.compress t1' in
                   uu____2290.FStar_Syntax_Syntax.n in
                 match uu____2289 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2307 -> aux true t1'
                 | uu____2314 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2329 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 let uu____2360 =
                   let uu____2361 = FStar_Syntax_Subst.compress t1' in
                   uu____2361.FStar_Syntax_Syntax.n in
                 match uu____2360 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2378 -> aux true t1'
                 | uu____2385 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2400 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 let uu____2445 =
                   let uu____2446 = FStar_Syntax_Subst.compress t1' in
                   uu____2446.FStar_Syntax_Syntax.n in
                 match uu____2445 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2463 -> aux true t1'
                 | uu____2470 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2485 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2500 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2515 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2530 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2545 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2572 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2603 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2634 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2661 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2698 ->
              let uu____2705 =
                let uu____2706 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2707 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2706 uu____2707 in
              failwith uu____2705
          | FStar_Syntax_Syntax.Tm_ascribed uu____2722 ->
              let uu____2749 =
                let uu____2750 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2751 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2750 uu____2751 in
              failwith uu____2749
          | FStar_Syntax_Syntax.Tm_delayed uu____2766 ->
              let uu____2791 =
                let uu____2792 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2793 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2792 uu____2793 in
              failwith uu____2791
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2808 =
                let uu____2809 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2810 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2809 uu____2810 in
              failwith uu____2808 in
        let uu____2825 = whnf env t1 in aux false uu____2825
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2834 =
        let uu____2849 = empty_worklist env in
        base_and_refinement env uu____2849 t in
      FStar_All.pipe_right uu____2834 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2884 = FStar_Syntax_Syntax.null_bv t in
    (uu____2884, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2893 .
    FStar_TypeChecker_Env.env ->
      'Auu____2893 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2910 = base_and_refinement env wl t in
        match uu____2910 with
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
  fun uu____2990  ->
    match uu____2990 with
    | (t_base,refopt) ->
        let uu____3017 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____3017 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____3052 =
      let uu____3055 =
        let uu____3058 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3081  ->
                  match uu____3081 with | (uu____3088,uu____3089,x) -> x)) in
        FStar_List.append wl.attempting uu____3058 in
      FStar_List.map (wl_prob_to_string wl) uu____3055 in
    FStar_All.pipe_right uu____3052 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3117 =
          let uu____3136 =
            let uu____3137 = FStar_Syntax_Subst.compress k in
            uu____3137.FStar_Syntax_Syntax.n in
          match uu____3136 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3202 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3202)
              else
                (let uu____3228 = FStar_Syntax_Util.abs_formals t in
                 match uu____3228 with
                 | (ys',t1,uu____3257) ->
                     let uu____3262 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3262))
          | uu____3303 ->
              let uu____3304 =
                let uu____3315 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3315) in
              ((ys, t), uu____3304) in
        match uu____3117 with
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
                 let uu____3394 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3394 c in
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
            let uu____3427 = p_guard prob in
            match uu____3427 with
            | (uu____3432,uv) ->
                ((let uu____3435 =
                    let uu____3436 = FStar_Syntax_Subst.compress uv in
                    uu____3436.FStar_Syntax_Syntax.n in
                  match uu____3435 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3468 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3468
                        then
                          let uu____3469 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3470 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3471 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3469
                            uu____3470 uu____3471
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3473 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___176_3476 = wl in
                  {
                    attempting = (uu___176_3476.attempting);
                    wl_deferred = (uu___176_3476.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___176_3476.defer_ok);
                    smt_ok = (uu___176_3476.smt_ok);
                    tcenv = (uu___176_3476.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3494 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3494
         then
           let uu____3495 = FStar_Util.string_of_int pid in
           let uu____3496 =
             let uu____3497 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3497 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3495 uu____3496
         else ());
        commit sol;
        (let uu___177_3504 = wl in
         {
           attempting = (uu___177_3504.attempting);
           wl_deferred = (uu___177_3504.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___177_3504.defer_ok);
           smt_ok = (uu___177_3504.smt_ok);
           tcenv = (uu___177_3504.tcenv)
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
            | (uu____3546,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3558 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3558 in
          (let uu____3564 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3564
           then
             let uu____3565 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3566 =
               let uu____3567 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3567 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3565 uu____3566
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
        let uu____3602 =
          let uu____3609 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3609 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3602
          (FStar_Util.for_some
             (fun uu____3645  ->
                match uu____3645 with
                | (uv,uu____3651) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3664 'Auu____3665 .
    'Auu____3665 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3664)
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
            let uu____3697 = occurs wl uk t in Prims.op_Negation uu____3697 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3704 =
                 let uu____3705 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3706 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3705 uu____3706 in
               FStar_Pervasives_Native.Some uu____3704) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3723 'Auu____3724 .
    'Auu____3724 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3723)
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
            let uu____3778 = occurs_check env wl uk t in
            match uu____3778 with
            | (occurs_ok,msg) ->
                let uu____3809 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3809, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3836 'Auu____3837 .
    (FStar_Syntax_Syntax.bv,'Auu____3837) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3836) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3836) FStar_Pervasives_Native.tuple2
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
      let uu____3921 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3975  ->
                fun uu____3976  ->
                  match (uu____3975, uu____3976) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4057 =
                        let uu____4058 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____4058 in
                      if uu____4057
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4083 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4083
                         then
                           let uu____4096 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4096)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3921 with | (isect,uu____4137) -> FStar_List.rev isect
let binders_eq:
  'Auu____4166 'Auu____4167 .
    (FStar_Syntax_Syntax.bv,'Auu____4167) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4166) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4222  ->
              fun uu____4223  ->
                match (uu____4222, uu____4223) with
                | ((a,uu____4241),(b,uu____4243)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4262 'Auu____4263 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4263) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4262)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4262)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4314 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4328  ->
                      match uu____4328 with
                      | (b,uu____4334) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4314
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4350 -> FStar_Pervasives_Native.None
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
            let uu____4425 = pat_var_opt env seen hd1 in
            (match uu____4425 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4439 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4439
                   then
                     let uu____4440 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4440
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4459 =
      let uu____4460 = FStar_Syntax_Subst.compress t in
      uu____4460.FStar_Syntax_Syntax.n in
    match uu____4459 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4463 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4480;
           FStar_Syntax_Syntax.pos = uu____4481;
           FStar_Syntax_Syntax.vars = uu____4482;_},uu____4483)
        -> true
    | uu____4520 -> false
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
           FStar_Syntax_Syntax.pos = uu____4645;
           FStar_Syntax_Syntax.vars = uu____4646;_},args)
        -> (t, uv, k, args)
    | uu____4714 -> failwith "Not a flex-uvar"
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
      let uu____4793 = destruct_flex_t t in
      match uu____4793 with
      | (t1,uv,k,args) ->
          let uu____4908 = pat_vars env [] args in
          (match uu____4908 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____5006 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5088 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5125 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5130 -> false
let head_match: match_result -> match_result =
  fun uu___153_5134  ->
    match uu___153_5134 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5149 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5160 ->
          let uu____5161 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5161 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5172 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5193 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5202 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5229 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5230 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5231 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5248 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5261 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5285) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5291,uu____5292) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5334) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5355;
             FStar_Syntax_Syntax.index = uu____5356;
             FStar_Syntax_Syntax.sort = t2;_},uu____5358)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5365 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5366 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5367 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5380 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5398 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5398
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
            let uu____5422 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5422
            then FullMatch
            else
              (let uu____5424 =
                 let uu____5433 =
                   let uu____5436 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5436 in
                 let uu____5437 =
                   let uu____5440 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5440 in
                 (uu____5433, uu____5437) in
               MisMatch uu____5424)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5446),FStar_Syntax_Syntax.Tm_uinst (g,uu____5448)) ->
            let uu____5457 = head_matches env f g in
            FStar_All.pipe_right uu____5457 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5466),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5468)) ->
            let uu____5517 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5517
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5524),FStar_Syntax_Syntax.Tm_refine (y,uu____5526)) ->
            let uu____5535 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5535 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5537),uu____5538) ->
            let uu____5543 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5543 head_match
        | (uu____5544,FStar_Syntax_Syntax.Tm_refine (x,uu____5546)) ->
            let uu____5551 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5551 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5552,FStar_Syntax_Syntax.Tm_type
           uu____5553) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5554,FStar_Syntax_Syntax.Tm_arrow uu____5555) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5581),FStar_Syntax_Syntax.Tm_app (head',uu____5583))
            ->
            let uu____5624 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5624 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5626),uu____5627) ->
            let uu____5648 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5648 head_match
        | (uu____5649,FStar_Syntax_Syntax.Tm_app (head1,uu____5651)) ->
            let uu____5672 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5672 head_match
        | uu____5673 ->
            let uu____5678 =
              let uu____5687 = delta_depth_of_term env t11 in
              let uu____5690 = delta_depth_of_term env t21 in
              (uu____5687, uu____5690) in
            MisMatch uu____5678
let head_matches_delta:
  'Auu____5707 .
    FStar_TypeChecker_Env.env ->
      'Auu____5707 ->
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
            let uu____5740 = FStar_Syntax_Util.head_and_args t in
            match uu____5740 with
            | (head1,uu____5758) ->
                let uu____5779 =
                  let uu____5780 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5780.FStar_Syntax_Syntax.n in
                (match uu____5779 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5786 =
                       let uu____5787 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5787 FStar_Option.isSome in
                     if uu____5786
                     then
                       let uu____5806 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5806
                         (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                     else FStar_Pervasives_Native.None
                 | uu____5810 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5913)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5931 =
                     let uu____5940 = maybe_inline t11 in
                     let uu____5943 = maybe_inline t21 in
                     (uu____5940, uu____5943) in
                   match uu____5931 with
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
                (uu____5980,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5998 =
                     let uu____6007 = maybe_inline t11 in
                     let uu____6010 = maybe_inline t21 in
                     (uu____6007, uu____6010) in
                   match uu____5998 with
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
                let uu____6053 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____6053 with
                 | FStar_Pervasives_Native.None  -> fail r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t11 in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21 in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
                let uu____6076 =
                  if d1_greater_than_d2
                  then
                    let t1' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                        FStar_TypeChecker_Normalize.Weak;
                        FStar_TypeChecker_Normalize.HNF] env wl t11 in
                    (t1', t21)
                  else
                    (let t2' =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21 in
                     (t11, t2')) in
                (match uu____6076 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6100 -> fail r
            | uu____6109 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6143 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6181 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___154_6195  ->
    match uu___154_6195 with
    | T (t,uu____6197) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6215 = FStar_Syntax_Util.type_u () in
      match uu____6215 with
      | (t,uu____6221) ->
          let uu____6222 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6222
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6235 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6235 FStar_Pervasives_Native.fst
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
        let uu____6301 = head_matches env t1 t' in
        match uu____6301 with
        | MisMatch uu____6302 -> false
        | uu____6311 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6407,imp),T (t2,uu____6410)) -> (t2, imp)
                     | uu____6429 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6496  ->
                    match uu____6496 with
                    | (t2,uu____6510) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6553 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6553 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6628))::tcs2) ->
                       aux
                         (((let uu___178_6663 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_6663.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_6663.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6681 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___155_6734 =
                 match uu___155_6734 with
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
               let uu____6851 = decompose1 [] bs1 in
               (rebuild, matches, uu____6851))
      | uu____6900 ->
          let rebuild uu___156_6906 =
            match uu___156_6906 with
            | [] -> t1
            | uu____6909 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___157_6941  ->
    match uu___157_6941 with
    | T (t,uu____6943) -> t
    | uu____6952 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___158_6956  ->
    match uu___158_6956 with
    | T (t,uu____6958) -> FStar_Syntax_Syntax.as_arg t
    | uu____6967 -> failwith "Impossible"
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
              | (uu____7078,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7103 = new_uvar r scope1 k in
                  (match uu____7103 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7121 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7138 =
                         let uu____7139 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_48  ->
                              FStar_TypeChecker_Common.TProb _0_48)
                           uu____7139 in
                       ((T (gi_xs, mk_kind)), uu____7138))
              | (uu____7152,uu____7153,C uu____7154) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7301 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7318;
                         FStar_Syntax_Syntax.vars = uu____7319;_})
                        ->
                        let uu____7342 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7342 with
                         | (T (gi_xs,uu____7366),prob) ->
                             let uu____7376 =
                               let uu____7377 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_49  -> C _0_49)
                                 uu____7377 in
                             (uu____7376, [prob])
                         | uu____7380 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7395;
                         FStar_Syntax_Syntax.vars = uu____7396;_})
                        ->
                        let uu____7419 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7419 with
                         | (T (gi_xs,uu____7443),prob) ->
                             let uu____7453 =
                               let uu____7454 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____7454 in
                             (uu____7453, [prob])
                         | uu____7457 -> failwith "impossible")
                    | (uu____7468,uu____7469,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7471;
                         FStar_Syntax_Syntax.vars = uu____7472;_})
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
                        let uu____7603 =
                          let uu____7612 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7612 FStar_List.unzip in
                        (match uu____7603 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7666 =
                                 let uu____7667 =
                                   let uu____7670 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7670 un_T in
                                 let uu____7671 =
                                   let uu____7680 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7680
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7667;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7671;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7666 in
                             ((C gi_xs), sub_probs))
                    | uu____7689 ->
                        let uu____7702 = sub_prob scope1 args q in
                        (match uu____7702 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7301 with
                   | (tc,probs) ->
                       let uu____7733 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7796,uu____7797),T
                            (t,uu____7799)) ->
                             let b1 =
                               ((let uu___179_7836 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___179_7836.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___179_7836.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7837 =
                               let uu____7844 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7844 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7837)
                         | uu____7879 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7733 with
                        | (bopt,scope2,args1) ->
                            let uu____7963 = aux scope2 args1 qs2 in
                            (match uu____7963 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____8000 =
                                         let uu____8003 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____8003 in
                                       FStar_Syntax_Util.mk_conj_l uu____8000
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____8026 =
                                         let uu____8029 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____8030 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____8029 :: uu____8030 in
                                       FStar_Syntax_Util.mk_conj_l uu____8026 in
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
  'Auu____8101 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8101)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8101)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___180_8122 = p in
      let uu____8127 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8128 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___180_8122.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8127;
        FStar_TypeChecker_Common.relation =
          (uu___180_8122.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8128;
        FStar_TypeChecker_Common.element =
          (uu___180_8122.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___180_8122.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___180_8122.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___180_8122.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___180_8122.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___180_8122.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8142 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8142
            (fun _0_51  -> FStar_TypeChecker_Common.TProb _0_51)
      | FStar_TypeChecker_Common.CProb uu____8151 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8173 = compress_prob wl pr in
        FStar_All.pipe_right uu____8173 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8183 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8183 with
           | (lh,uu____8203) ->
               let uu____8224 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8224 with
                | (rh,uu____8244) ->
                    let uu____8265 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8282,FStar_Syntax_Syntax.Tm_uvar uu____8283)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8320,uu____8321)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8342,FStar_Syntax_Syntax.Tm_uvar uu____8343)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8364,uu____8365)
                          ->
                          let uu____8382 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8382 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8445 ->
                                    let rank =
                                      let uu____8455 = is_top_level_prob prob in
                                      if uu____8455
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8457 =
                                      let uu___181_8462 = tp in
                                      let uu____8467 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___181_8462.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___181_8462.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___181_8462.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8467;
                                        FStar_TypeChecker_Common.element =
                                          (uu___181_8462.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___181_8462.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___181_8462.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___181_8462.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___181_8462.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___181_8462.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8457)))
                      | (uu____8482,FStar_Syntax_Syntax.Tm_uvar uu____8483)
                          ->
                          let uu____8500 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8500 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8563 ->
                                    let uu____8572 =
                                      let uu___182_8579 = tp in
                                      let uu____8584 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___182_8579.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8584;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___182_8579.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___182_8579.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___182_8579.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___182_8579.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___182_8579.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___182_8579.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___182_8579.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___182_8579.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8572)))
                      | (uu____8605,uu____8606) -> (rigid_rigid, tp) in
                    (match uu____8265 with
                     | (rank,tp1) ->
                         let uu____8625 =
                           FStar_All.pipe_right
                             (let uu___183_8631 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___183_8631.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___183_8631.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___183_8631.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___183_8631.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___183_8631.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___183_8631.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___183_8631.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___183_8631.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___183_8631.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_52  ->
                                FStar_TypeChecker_Common.TProb _0_52) in
                         (rank, uu____8625))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8641 =
            FStar_All.pipe_right
              (let uu___184_8647 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___184_8647.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___184_8647.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___184_8647.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___184_8647.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___184_8647.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___184_8647.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___184_8647.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___184_8647.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___184_8647.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_53  -> FStar_TypeChecker_Common.CProb _0_53) in
          (rigid_rigid, uu____8641)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8703 probs =
      match uu____8703 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8756 = rank wl hd1 in
               (match uu____8756 with
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
    match projectee with | UDeferred _0 -> true | uu____8866 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8880 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8894 -> false
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
                        let uu____8939 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8939 with
                        | (k,uu____8945) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8955 -> false)))
            | uu____8956 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____9007 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____9007 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____9010 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____9020 =
                     let uu____9021 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____9022 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____9021
                       uu____9022 in
                   UFailed uu____9020)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9042 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9042 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9064 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____9064 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____9067 ->
                let uu____9072 =
                  let uu____9073 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____9074 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9073
                    uu____9074 msg in
                UFailed uu____9072 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9075,uu____9076) ->
              let uu____9077 =
                let uu____9078 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9079 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9078 uu____9079 in
              failwith uu____9077
          | (FStar_Syntax_Syntax.U_unknown ,uu____9080) ->
              let uu____9081 =
                let uu____9082 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9083 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9082 uu____9083 in
              failwith uu____9081
          | (uu____9084,FStar_Syntax_Syntax.U_bvar uu____9085) ->
              let uu____9086 =
                let uu____9087 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9088 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9087 uu____9088 in
              failwith uu____9086
          | (uu____9089,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9090 =
                let uu____9091 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9092 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9091 uu____9092 in
              failwith uu____9090
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9116 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9116
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9138 = occurs_univ v1 u3 in
              if uu____9138
              then
                let uu____9139 =
                  let uu____9140 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9141 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9140 uu____9141 in
                try_umax_components u11 u21 uu____9139
              else
                (let uu____9143 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9143)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9163 = occurs_univ v1 u3 in
              if uu____9163
              then
                let uu____9164 =
                  let uu____9165 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9166 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9165 uu____9166 in
                try_umax_components u11 u21 uu____9164
              else
                (let uu____9168 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9168)
          | (FStar_Syntax_Syntax.U_max uu____9177,uu____9178) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9184 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9184
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9186,FStar_Syntax_Syntax.U_max uu____9187) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9193 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9193
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9195,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9196,FStar_Syntax_Syntax.U_name
             uu____9197) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9198) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9199) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9200,FStar_Syntax_Syntax.U_succ
             uu____9201) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9202,FStar_Syntax_Syntax.U_zero
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
      let uu____9296 = bc1 in
      match uu____9296 with
      | (bs1,mk_cod1) ->
          let uu____9337 = bc2 in
          (match uu____9337 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9407 = FStar_Util.first_N n1 bs in
                 match uu____9407 with
                 | (bs3,rest) ->
                     let uu____9432 = mk_cod rest in (bs3, uu____9432) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9461 =
                   let uu____9468 = mk_cod1 [] in (bs1, uu____9468) in
                 let uu____9471 =
                   let uu____9478 = mk_cod2 [] in (bs2, uu____9478) in
                 (uu____9461, uu____9471)
               else
                 if l1 > l2
                 then
                   (let uu____9520 = curry l2 bs1 mk_cod1 in
                    let uu____9533 =
                      let uu____9540 = mk_cod2 [] in (bs2, uu____9540) in
                    (uu____9520, uu____9533))
                 else
                   (let uu____9556 =
                      let uu____9563 = mk_cod1 [] in (bs1, uu____9563) in
                    let uu____9566 = curry l1 bs2 mk_cod2 in
                    (uu____9556, uu____9566)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9687 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9687
       then
         let uu____9688 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9688
       else ());
      (let uu____9690 = next_prob probs in
       match uu____9690 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___185_9711 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___185_9711.wl_deferred);
               ctr = (uu___185_9711.ctr);
               defer_ok = (uu___185_9711.defer_ok);
               smt_ok = (uu___185_9711.smt_ok);
               tcenv = (uu___185_9711.tcenv)
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
                  let uu____9722 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9722 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9727 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9727 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9732,uu____9733) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9750 ->
                let uu____9759 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9818  ->
                          match uu____9818 with
                          | (c,uu____9826,uu____9827) -> c < probs.ctr)) in
                (match uu____9759 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9868 =
                            FStar_List.map
                              (fun uu____9883  ->
                                 match uu____9883 with
                                 | (uu____9894,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9868
                      | uu____9897 ->
                          let uu____9906 =
                            let uu___186_9907 = probs in
                            let uu____9908 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9929  ->
                                      match uu____9929 with
                                      | (uu____9936,uu____9937,y) -> y)) in
                            {
                              attempting = uu____9908;
                              wl_deferred = rest;
                              ctr = (uu___186_9907.ctr);
                              defer_ok = (uu___186_9907.defer_ok);
                              smt_ok = (uu___186_9907.smt_ok);
                              tcenv = (uu___186_9907.tcenv)
                            } in
                          solve env uu____9906))))
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
            let uu____9944 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9944 with
            | USolved wl1 ->
                let uu____9946 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9946
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
                  let uu____9992 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9992 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9995 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10007;
                  FStar_Syntax_Syntax.vars = uu____10008;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10011;
                  FStar_Syntax_Syntax.vars = uu____10012;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10026,uu____10027) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10034,FStar_Syntax_Syntax.Tm_uinst uu____10035) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10042 -> USolved wl
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
            ((let uu____10052 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____10052
              then
                let uu____10053 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10053 msg
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
        (let uu____10062 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10062
         then
           let uu____10063 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10063
         else ());
        (let uu____10065 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____10065 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10127 = head_matches_delta env () t1 t2 in
               match uu____10127 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10168 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10217 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10232 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10233 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10232, uu____10233)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10238 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10239 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10238, uu____10239) in
                        (match uu____10217 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10265 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_54  ->
                                    FStar_TypeChecker_Common.TProb _0_54)
                                 uu____10265 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10296 =
                                    let uu____10305 =
                                      let uu____10308 =
                                        let uu____10311 =
                                          let uu____10312 =
                                            let uu____10319 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10319) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10312 in
                                        FStar_Syntax_Syntax.mk uu____10311 in
                                      uu____10308
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10327 =
                                      let uu____10330 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10330] in
                                    (uu____10305, uu____10327) in
                                  FStar_Pervasives_Native.Some uu____10296
                              | (uu____10343,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10345)) ->
                                  let uu____10350 =
                                    let uu____10357 =
                                      let uu____10360 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10360] in
                                    (t11, uu____10357) in
                                  FStar_Pervasives_Native.Some uu____10350
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10370),uu____10371) ->
                                  let uu____10376 =
                                    let uu____10383 =
                                      let uu____10386 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10386] in
                                    (t21, uu____10383) in
                                  FStar_Pervasives_Native.Some uu____10376
                              | uu____10395 ->
                                  let uu____10400 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10400 with
                                   | (head1,uu____10424) ->
                                       let uu____10445 =
                                         let uu____10446 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10446.FStar_Syntax_Syntax.n in
                                       (match uu____10445 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10457;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10459;_}
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
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11 in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21 in
                                            disjoin t12 t22
                                        | uu____10466 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10479) ->
                  let uu____10504 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___159_10530  ->
                            match uu___159_10530 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10537 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10537 with
                                      | (u',uu____10553) ->
                                          let uu____10574 =
                                            let uu____10575 = whnf env u' in
                                            uu____10575.FStar_Syntax_Syntax.n in
                                          (match uu____10574 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10579) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10604 -> false))
                                 | uu____10605 -> false)
                            | uu____10608 -> false)) in
                  (match uu____10504 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10642 tps =
                         match uu____10642 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10690 =
                                    let uu____10699 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10699 in
                                  (match uu____10690 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10734 -> FStar_Pervasives_Native.None) in
                       let uu____10743 =
                         let uu____10752 =
                           let uu____10759 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10759, []) in
                         make_lower_bound uu____10752 lower_bounds in
                       (match uu____10743 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10771 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10771
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
                            ((let uu____10791 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10791
                              then
                                let wl' =
                                  let uu___187_10793 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___187_10793.wl_deferred);
                                    ctr = (uu___187_10793.ctr);
                                    defer_ok = (uu___187_10793.defer_ok);
                                    smt_ok = (uu___187_10793.smt_ok);
                                    tcenv = (uu___187_10793.tcenv)
                                  } in
                                let uu____10794 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10794
                              else ());
                             (let uu____10796 =
                                solve_t env eq_prob
                                  (let uu___188_10798 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___188_10798.wl_deferred);
                                     ctr = (uu___188_10798.ctr);
                                     defer_ok = (uu___188_10798.defer_ok);
                                     smt_ok = (uu___188_10798.smt_ok);
                                     tcenv = (uu___188_10798.tcenv)
                                   }) in
                              match uu____10796 with
                              | Success uu____10801 ->
                                  let wl1 =
                                    let uu___189_10803 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___189_10803.wl_deferred);
                                      ctr = (uu___189_10803.ctr);
                                      defer_ok = (uu___189_10803.defer_ok);
                                      smt_ok = (uu___189_10803.smt_ok);
                                      tcenv = (uu___189_10803.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10805 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10810 -> FStar_Pervasives_Native.None))))
              | uu____10811 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10820 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10820
         then
           let uu____10821 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10821
         else ());
        (let uu____10823 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10823 with
         | (u,args) ->
             let uu____10862 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10862 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10903 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10903 with
                    | (h1,args1) ->
                        let uu____10944 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10944 with
                         | (h2,uu____10964) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10991 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10991
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11009 =
                                          let uu____11012 =
                                            let uu____11013 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_55  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_55) uu____11013 in
                                          [uu____11012] in
                                        FStar_Pervasives_Native.Some
                                          uu____11009))
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
                                       (let uu____11046 =
                                          let uu____11049 =
                                            let uu____11050 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____11050 in
                                          [uu____11049] in
                                        FStar_Pervasives_Native.Some
                                          uu____11046))
                                  else FStar_Pervasives_Native.None
                              | uu____11064 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11154 =
                               let uu____11163 =
                                 let uu____11166 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11166 in
                               (uu____11163, m1) in
                             FStar_Pervasives_Native.Some uu____11154)
                    | (uu____11179,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11181)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11229),uu____11230) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11277 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11330) ->
                       let uu____11355 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___160_11381  ->
                                 match uu___160_11381 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11388 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11388 with
                                           | (u',uu____11404) ->
                                               let uu____11425 =
                                                 let uu____11426 =
                                                   whnf env u' in
                                                 uu____11426.FStar_Syntax_Syntax.n in
                                               (match uu____11425 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11430) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11455 -> false))
                                      | uu____11456 -> false)
                                 | uu____11459 -> false)) in
                       (match uu____11355 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11497 tps =
                              match uu____11497 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11559 =
                                         let uu____11570 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11570 in
                                       (match uu____11559 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11621 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11632 =
                              let uu____11643 =
                                let uu____11652 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11652, []) in
                              make_upper_bound uu____11643 upper_bounds in
                            (match uu____11632 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11666 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11666
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
                                 ((let uu____11692 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11692
                                   then
                                     let wl' =
                                       let uu___190_11694 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___190_11694.wl_deferred);
                                         ctr = (uu___190_11694.ctr);
                                         defer_ok = (uu___190_11694.defer_ok);
                                         smt_ok = (uu___190_11694.smt_ok);
                                         tcenv = (uu___190_11694.tcenv)
                                       } in
                                     let uu____11695 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11695
                                   else ());
                                  (let uu____11697 =
                                     solve_t env eq_prob
                                       (let uu___191_11699 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___191_11699.wl_deferred);
                                          ctr = (uu___191_11699.ctr);
                                          defer_ok =
                                            (uu___191_11699.defer_ok);
                                          smt_ok = (uu___191_11699.smt_ok);
                                          tcenv = (uu___191_11699.tcenv)
                                        }) in
                                   match uu____11697 with
                                   | Success uu____11702 ->
                                       let wl1 =
                                         let uu___192_11704 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___192_11704.wl_deferred);
                                           ctr = (uu___192_11704.ctr);
                                           defer_ok =
                                             (uu___192_11704.defer_ok);
                                           smt_ok = (uu___192_11704.smt_ok);
                                           tcenv = (uu___192_11704.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11706 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11711 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11712 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11803 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11803
                      then
                        let uu____11804 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11804
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___193_11858 = hd1 in
                      let uu____11859 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___193_11858.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___193_11858.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11859
                      } in
                    let hd21 =
                      let uu___194_11863 = hd2 in
                      let uu____11864 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___194_11863.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___194_11863.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11864
                      } in
                    let prob =
                      let uu____11868 =
                        let uu____11873 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11873 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_57  -> FStar_TypeChecker_Common.TProb _0_57)
                        uu____11868 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11884 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11884 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11888 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11888 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11918 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11923 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11918 uu____11923 in
                         ((let uu____11933 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11933
                           then
                             let uu____11934 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11935 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11934 uu____11935
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11958 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11968 = aux scope env [] bs1 bs2 in
              match uu____11968 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11992 = compress_tprob wl problem in
        solve_t' env uu____11992 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____12025 = head_matches_delta env1 wl1 t1 t2 in
          match uu____12025 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12056,uu____12057) ->
                   let rec may_relate head3 =
                     let uu____12082 =
                       let uu____12083 = FStar_Syntax_Subst.compress head3 in
                       uu____12083.FStar_Syntax_Syntax.n in
                     match uu____12082 with
                     | FStar_Syntax_Syntax.Tm_name uu____12086 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12087 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12112,uu____12113) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12155) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12161) ->
                         may_relate t
                     | uu____12166 -> false in
                   let uu____12167 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12167
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
                                let uu____12184 =
                                  let uu____12185 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12185 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12184 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12187 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12187
                   else
                     (let uu____12189 =
                        let uu____12190 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12191 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12190 uu____12191 in
                      giveup env1 uu____12189 orig)
               | (uu____12192,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___195_12206 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___195_12206.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___195_12206.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___195_12206.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___195_12206.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___195_12206.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___195_12206.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___195_12206.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___195_12206.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12207,FStar_Pervasives_Native.None ) ->
                   ((let uu____12219 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12219
                     then
                       let uu____12220 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12221 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12222 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12223 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12220
                         uu____12221 uu____12222 uu____12223
                     else ());
                    (let uu____12225 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12225 with
                     | (head11,args1) ->
                         let uu____12262 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12262 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12316 =
                                  let uu____12317 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12318 = args_to_string args1 in
                                  let uu____12319 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12320 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12317 uu____12318 uu____12319
                                    uu____12320 in
                                giveup env1 uu____12316 orig
                              else
                                (let uu____12322 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12328 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12328 = FStar_Syntax_Util.Equal) in
                                 if uu____12322
                                 then
                                   let uu____12329 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12329 with
                                   | USolved wl2 ->
                                       let uu____12331 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12331
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12335 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12335 with
                                    | (base1,refinement1) ->
                                        let uu____12372 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12372 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12453 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12453 with
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
                                                           (fun uu____12475 
                                                              ->
                                                              fun uu____12476
                                                                 ->
                                                                match 
                                                                  (uu____12475,
                                                                    uu____12476)
                                                                with
                                                                | ((a,uu____12494),
                                                                   (a',uu____12496))
                                                                    ->
                                                                    let uu____12505
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
                                                                    uu____12505)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12515 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12515 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12521 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___196_12569 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___196_12569.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12608 =
          match uu____12608 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12824  ->
                              match uu____12824 with
                              | (x,imp) ->
                                  let uu____12835 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12835, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12848 = FStar_Syntax_Util.type_u () in
                      match uu____12848 with
                      | (t1,uu____12854) ->
                          let uu____12855 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12855 in
                    let uu____12860 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12860 with
                     | (t',tm_u1) ->
                         let uu____12873 = destruct_flex_t t' in
                         (match uu____12873 with
                          | (uu____12910,u1,k1,uu____12913) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12972 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12972 in
                              let sol =
                                let uu____12976 =
                                  let uu____12985 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12985) in
                                TERM uu____12976 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13121 = pat_var_opt env pat_args hd1 in
                    (match uu____13121 with
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
                                    (fun uu____13184  ->
                                       match uu____13184 with
                                       | (x,uu____13190) ->
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
                            let uu____13205 =
                              let uu____13206 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____13206 in
                            if uu____13205
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____13218 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____13218 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____13233::uu____13234) ->
                    let uu____13265 =
                      let uu____13278 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13278 in
                    (match uu____13265 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13317 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13324::uu____13325,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13360 =
                let uu____13373 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13373 in
              (match uu____13360 with
               | (all_formals,res_t) ->
                   let uu____13398 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13398 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13432 = lhs in
          match uu____13432 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13442 ->
                    let uu____13443 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13443 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13472 = p in
          match uu____13472 with
          | (((u,k),xs,c),ps,(h,uu____13483,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13565 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13565 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13588 = h gs_xs in
                     let uu____13589 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59) in
                     FStar_Syntax_Util.abs xs1 uu____13588 uu____13589 in
                   ((let uu____13595 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13595
                     then
                       let uu____13596 =
                         let uu____13599 =
                           let uu____13600 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13600
                             (FStar_String.concat "\n\t") in
                         let uu____13605 =
                           let uu____13608 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13609 =
                             let uu____13612 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13613 =
                               let uu____13616 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13617 =
                                 let uu____13620 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13621 =
                                   let uu____13624 =
                                     let uu____13625 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13625
                                       (FStar_String.concat ", ") in
                                   let uu____13630 =
                                     let uu____13633 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13633] in
                                   uu____13624 :: uu____13630 in
                                 uu____13620 :: uu____13621 in
                               uu____13616 :: uu____13617 in
                             uu____13612 :: uu____13613 in
                           uu____13608 :: uu____13609 in
                         uu____13599 :: uu____13605 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13596
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___161_13654 =
          match uu___161_13654 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13686 = p in
          match uu____13686 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13777 = FStar_List.nth ps i in
              (match uu____13777 with
               | (pi,uu____13781) ->
                   let uu____13786 = FStar_List.nth xs i in
                   (match uu____13786 with
                    | (xi,uu____13798) ->
                        let rec gs k =
                          let uu____13811 =
                            let uu____13824 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13824 in
                          match uu____13811 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13899)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13912 = new_uvar r xs k_a in
                                    (match uu____13912 with
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
                                         let uu____13934 = aux subst2 tl1 in
                                         (match uu____13934 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13961 =
                                                let uu____13964 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13964 :: gi_xs' in
                                              let uu____13965 =
                                                let uu____13968 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13968 :: gi_ps' in
                                              (uu____13961, uu____13965))) in
                              aux [] bs in
                        let uu____13973 =
                          let uu____13974 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13974 in
                        if uu____13973
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13978 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13978 with
                           | (g_xs,uu____13990) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____14001 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____14002 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_60  ->
                                        FStar_Pervasives_Native.Some _0_60) in
                                 FStar_Syntax_Util.abs xs uu____14001
                                   uu____14002 in
                               let sub1 =
                                 let uu____14008 =
                                   let uu____14013 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____14016 =
                                     let uu____14019 =
                                       FStar_List.map
                                         (fun uu____14034  ->
                                            match uu____14034 with
                                            | (uu____14043,uu____14044,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____14019 in
                                   mk_problem (p_scope orig) orig uu____14013
                                     (p_rel orig) uu____14016
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____14008 in
                               ((let uu____14059 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14059
                                 then
                                   let uu____14060 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____14061 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14060 uu____14061
                                 else ());
                                (let wl2 =
                                   let uu____14064 =
                                     let uu____14067 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____14067 in
                                   solve_prob orig uu____14064
                                     [TERM (u, proj)] wl1 in
                                 let uu____14076 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____14076))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14107 = lhs in
          match uu____14107 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14143 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14143 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14176 =
                        let uu____14223 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14223) in
                      FStar_Pervasives_Native.Some uu____14176
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14367 =
                           let uu____14374 =
                             let uu____14375 = FStar_Syntax_Subst.compress k1 in
                             uu____14375.FStar_Syntax_Syntax.n in
                           (uu____14374, args) in
                         match uu____14367 with
                         | (uu____14386,[]) ->
                             let uu____14389 =
                               let uu____14400 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14400) in
                             FStar_Pervasives_Native.Some uu____14389
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14421,uu____14422) ->
                             let uu____14443 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14443 with
                              | (uv1,uv_args) ->
                                  let uu____14486 =
                                    let uu____14487 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14487.FStar_Syntax_Syntax.n in
                                  (match uu____14486 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14497) ->
                                       let uu____14522 =
                                         pat_vars env [] uv_args in
                                       (match uu____14522 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14549  ->
                                                      let uu____14550 =
                                                        let uu____14551 =
                                                          let uu____14552 =
                                                            let uu____14557 =
                                                              let uu____14558
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14558
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14557 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14552 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14551 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14550)) in
                                            let c1 =
                                              let uu____14568 =
                                                let uu____14569 =
                                                  let uu____14574 =
                                                    let uu____14575 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14575
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14574 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14569 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14568 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14588 =
                                                let uu____14591 =
                                                  let uu____14592 =
                                                    let uu____14595 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14595
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14592 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14591 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14588 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14613 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14618,uu____14619) ->
                             let uu____14638 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14638 with
                              | (uv1,uv_args) ->
                                  let uu____14681 =
                                    let uu____14682 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14682.FStar_Syntax_Syntax.n in
                                  (match uu____14681 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14692) ->
                                       let uu____14717 =
                                         pat_vars env [] uv_args in
                                       (match uu____14717 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14744  ->
                                                      let uu____14745 =
                                                        let uu____14746 =
                                                          let uu____14747 =
                                                            let uu____14752 =
                                                              let uu____14753
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14753
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14752 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14747 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14746 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14745)) in
                                            let c1 =
                                              let uu____14763 =
                                                let uu____14764 =
                                                  let uu____14769 =
                                                    let uu____14770 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14770
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14769 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14764 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14763 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14783 =
                                                let uu____14786 =
                                                  let uu____14787 =
                                                    let uu____14790 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14790
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14787 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14786 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14783 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14808 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14815) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14856 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14856
                                 (fun _0_63  ->
                                    FStar_Pervasives_Native.Some _0_63)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14892 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14892 with
                                  | (args1,rest) ->
                                      let uu____14921 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14921 with
                                       | (xs2,c2) ->
                                           let uu____14934 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14934
                                             (fun uu____14958  ->
                                                match uu____14958 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14998 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14998 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____15066 =
                                        let uu____15071 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15071 in
                                      FStar_All.pipe_right uu____15066
                                        (fun _0_64  ->
                                           FStar_Pervasives_Native.Some _0_64))
                         | uu____15086 ->
                             let uu____15093 =
                               let uu____15094 =
                                 let uu____15099 =
                                   let uu____15100 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____15101 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____15102 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____15100 uu____15101 uu____15102 in
                                 (uu____15099, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____15094 in
                             FStar_Exn.raise uu____15093 in
                       let uu____15109 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15109
                         (fun uu____15164  ->
                            match uu____15164 with
                            | (xs1,c1) ->
                                let uu____15213 =
                                  let uu____15254 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15254) in
                                FStar_Pervasives_Native.Some uu____15213)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15375 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15391 = project orig env wl1 i st in
                     match uu____15391 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15405) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15420 = imitate orig env wl1 st in
                  match uu____15420 with
                  | Failed uu____15425 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15456 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15456 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15481 =
                      let uu____15482 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15482 wl2 in
                    (match uu____15481 with
                     | Failed uu____15483 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15501 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15501 with
                | (hd1,uu____15517) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15538 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15551 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15552 -> true
                     | uu____15569 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15573 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15573
                         then true
                         else
                           ((let uu____15576 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15576
                             then
                               let uu____15577 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15577
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15597 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15597 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15610 =
                            let uu____15611 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15611 in
                          giveup_or_defer1 orig uu____15610
                        else
                          (let uu____15613 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15613
                           then
                             let uu____15614 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15614
                              then
                                let uu____15615 = subterms args_lhs in
                                imitate' orig env wl1 uu____15615
                              else
                                ((let uu____15620 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15620
                                  then
                                    let uu____15621 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15622 = names_to_string fvs1 in
                                    let uu____15623 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15621 uu____15622 uu____15623
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
                               (let uu____15627 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15627
                                then
                                  ((let uu____15629 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15629
                                    then
                                      let uu____15630 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15631 = names_to_string fvs1 in
                                      let uu____15632 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15630 uu____15631 uu____15632
                                    else ());
                                   (let uu____15634 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15634))
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
                     (let uu____15645 =
                        let uu____15646 = FStar_Syntax_Free.names t1 in
                        check_head uu____15646 t2 in
                      if uu____15645
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15657 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15657
                          then
                            let uu____15658 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15659 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15658 uu____15659
                          else ());
                         (let uu____15667 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15667))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15744 uu____15745 r =
               match (uu____15744, uu____15745) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15943 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15943
                   then
                     let uu____15944 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15944
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15968 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15968
                       then
                         let uu____15969 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15970 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15971 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15972 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15973 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15969 uu____15970 uu____15971 uu____15972
                           uu____15973
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____16033 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____16033 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16047 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____16047 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16101 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16101 in
                                  let uu____16104 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16104 k3)
                           else
                             (let uu____16108 =
                                let uu____16109 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16110 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16111 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16109 uu____16110 uu____16111 in
                              failwith uu____16108) in
                       let uu____16112 =
                         let uu____16119 =
                           let uu____16132 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16132 in
                         match uu____16119 with
                         | (bs,k1') ->
                             let uu____16157 =
                               let uu____16170 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16170 in
                             (match uu____16157 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16198 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      uu____16198 in
                                  let uu____16207 =
                                    let uu____16212 =
                                      let uu____16213 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16213.FStar_Syntax_Syntax.n in
                                    let uu____16216 =
                                      let uu____16217 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16217.FStar_Syntax_Syntax.n in
                                    (uu____16212, uu____16216) in
                                  (match uu____16207 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16226,uu____16227) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16230,FStar_Syntax_Syntax.Tm_type
                                      uu____16231) -> (k2'_ys, [sub_prob])
                                   | uu____16234 ->
                                       let uu____16239 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16239 with
                                        | (t,uu____16251) ->
                                            let uu____16252 = new_uvar r zs t in
                                            (match uu____16252 with
                                             | (k_zs,uu____16264) ->
                                                 let kprob =
                                                   let uu____16266 =
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
                                                          _0_66) uu____16266 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16112 with
                       | (k_u',sub_probs) ->
                           let uu____16283 =
                             let uu____16294 =
                               let uu____16295 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16295 in
                             let uu____16304 =
                               let uu____16307 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16307 in
                             let uu____16310 =
                               let uu____16313 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16313 in
                             (uu____16294, uu____16304, uu____16310) in
                           (match uu____16283 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16332 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16332 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16351 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16351
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16355 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16355 with
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
             let solve_one_pat uu____16408 uu____16409 =
               match (uu____16408, uu____16409) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16527 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16527
                     then
                       let uu____16528 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16529 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16528 uu____16529
                     else ());
                    (let uu____16531 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16531
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16550  ->
                              fun uu____16551  ->
                                match (uu____16550, uu____16551) with
                                | ((a,uu____16569),(t21,uu____16571)) ->
                                    let uu____16580 =
                                      let uu____16585 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16585
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16580
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67))
                           xs args2 in
                       let guard =
                         let uu____16591 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16591 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16606 = occurs_check env wl (u1, k1) t21 in
                        match uu____16606 with
                        | (occurs_ok,uu____16614) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16622 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16622
                            then
                              let sol =
                                let uu____16624 =
                                  let uu____16633 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16633) in
                                TERM uu____16624 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16640 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16640
                               then
                                 let uu____16641 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16641 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16665,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16691 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16691
                                       then
                                         let uu____16692 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16692
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16699 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16701 = lhs in
             match uu____16701 with
             | (t1,u1,k1,args1) ->
                 let uu____16706 = rhs in
                 (match uu____16706 with
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
                       | uu____16746 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16756 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16756 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16774) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16781 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16781
                                    then
                                      let uu____16782 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16782
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16789 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16791 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16791
        then
          let uu____16792 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16792
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16796 = FStar_Util.physical_equality t1 t2 in
           if uu____16796
           then
             let uu____16797 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16797
           else
             ((let uu____16800 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16800
               then
                 let uu____16801 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16801
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16804,uu____16805) ->
                   let uu____16832 =
                     let uu___197_16833 = problem in
                     let uu____16834 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16833.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16834;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16833.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16833.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16833.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16833.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16833.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16833.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16833.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16833.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16832 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16835,uu____16836) ->
                   let uu____16843 =
                     let uu___197_16844 = problem in
                     let uu____16845 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16844.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16845;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16844.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16844.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16844.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16844.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16844.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16844.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16844.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16844.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16843 wl
               | (uu____16846,FStar_Syntax_Syntax.Tm_ascribed uu____16847) ->
                   let uu____16874 =
                     let uu___198_16875 = problem in
                     let uu____16876 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16875.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16875.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16875.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16876;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16875.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16875.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16875.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16875.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16875.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16875.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16874 wl
               | (uu____16877,FStar_Syntax_Syntax.Tm_meta uu____16878) ->
                   let uu____16885 =
                     let uu___198_16886 = problem in
                     let uu____16887 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16886.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16886.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16886.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16887;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16886.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16886.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16886.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16886.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16886.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16886.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16885 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16888,uu____16889) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16890,FStar_Syntax_Syntax.Tm_bvar uu____16891) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___162_16946 =
                     match uu___162_16946 with
                     | [] -> c
                     | bs ->
                         let uu____16968 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16968 in
                   let uu____16977 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16977 with
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
                                   let uu____17119 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17119
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17121 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.CProb _0_68)
                                   uu____17121))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___163_17197 =
                     match uu___163_17197 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17231 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17231 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17367 =
                                   let uu____17372 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17373 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17372
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17373 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17367))
               | (FStar_Syntax_Syntax.Tm_abs uu____17378,uu____17379) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17404 -> true
                     | uu____17421 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let force_eta t =
                     if is_abs t
                     then t
                     else
                       (let uu____17468 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17476 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17476.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17476.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17476.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17476.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17476.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17476.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17476.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17476.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17476.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17476.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17476.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17476.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17476.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17476.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17476.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17476.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17476.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17476.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17476.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17476.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17476.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17476.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17476.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17476.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17476.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17476.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17476.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17476.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17476.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17476.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17468 with
                        | (uu____17479,ty,uu____17481) ->
                            let uu____17482 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17482) in
                   let uu____17483 =
                     let uu____17500 = maybe_eta t1 in
                     let uu____17507 = maybe_eta t2 in
                     (uu____17500, uu____17507) in
                   (match uu____17483 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17549 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17549.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17549.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17549.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17549.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17549.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17549.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17549.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17549.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17572 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17572
                        then
                          let uu____17573 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17573 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17588 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17588.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17588.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17588.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17588.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17588.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17588.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17588.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17588.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17612 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17612
                        then
                          let uu____17613 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17613 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17628 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17628.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17628.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17628.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17628.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17628.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17628.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17628.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17628.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17632 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17649,FStar_Syntax_Syntax.Tm_abs uu____17650) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17675 -> true
                     | uu____17692 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let force_eta t =
                     if is_abs t
                     then t
                     else
                       (let uu____17739 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17747 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17747.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17747.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17747.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17747.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17747.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17747.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17747.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17747.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17747.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17747.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17747.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17747.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17747.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17747.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17747.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17747.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17747.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17747.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17747.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17747.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17747.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17747.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17747.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17747.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17747.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17747.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17747.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17747.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17747.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17747.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17739 with
                        | (uu____17750,ty,uu____17752) ->
                            let uu____17753 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17753) in
                   let uu____17754 =
                     let uu____17771 = maybe_eta t1 in
                     let uu____17778 = maybe_eta t2 in
                     (uu____17771, uu____17778) in
                   (match uu____17754 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17820 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17820.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17820.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17820.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17820.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17820.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17820.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17820.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17820.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17843 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17843
                        then
                          let uu____17844 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17844 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17859 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17859.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17859.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17859.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17859.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17859.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17859.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17859.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17859.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17883 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17883
                        then
                          let uu____17884 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17884 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17899 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17899.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17899.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17899.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17899.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17899.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17899.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17899.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17899.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17903 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17920,FStar_Syntax_Syntax.Tm_refine uu____17921) ->
                   let uu____17934 = as_refinement env wl t1 in
                   (match uu____17934 with
                    | (x1,phi1) ->
                        let uu____17941 = as_refinement env wl t2 in
                        (match uu____17941 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17949 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_70  ->
                                    FStar_TypeChecker_Common.TProb _0_70)
                                 uu____17949 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17987 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17987
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17991 =
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
                                 let uu____17997 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17997 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____18006 =
                                   let uu____18011 =
                                     let uu____18012 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____18012 :: (p_scope orig) in
                                   mk_problem uu____18011 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.TProb _0_71)
                                   uu____18006 in
                               let uu____18017 =
                                 solve env1
                                   (let uu___202_18019 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___202_18019.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___202_18019.smt_ok);
                                      tcenv = (uu___202_18019.tcenv)
                                    }) in
                               (match uu____18017 with
                                | Failed uu____18026 -> fallback ()
                                | Success uu____18031 ->
                                    let guard =
                                      let uu____18035 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____18040 =
                                        let uu____18041 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____18041
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____18035
                                        uu____18040 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___203_18050 = wl1 in
                                      {
                                        attempting =
                                          (uu___203_18050.attempting);
                                        wl_deferred =
                                          (uu___203_18050.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___203_18050.defer_ok);
                                        smt_ok = (uu___203_18050.smt_ok);
                                        tcenv = (uu___203_18050.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18052,FStar_Syntax_Syntax.Tm_uvar uu____18053) ->
                   let uu____18086 = destruct_flex_t t1 in
                   let uu____18087 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18086 uu____18087
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18088;
                     FStar_Syntax_Syntax.pos = uu____18089;
                     FStar_Syntax_Syntax.vars = uu____18090;_},uu____18091),FStar_Syntax_Syntax.Tm_uvar
                  uu____18092) ->
                   let uu____18145 = destruct_flex_t t1 in
                   let uu____18146 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18145 uu____18146
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18147,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18148;
                     FStar_Syntax_Syntax.pos = uu____18149;
                     FStar_Syntax_Syntax.vars = uu____18150;_},uu____18151))
                   ->
                   let uu____18204 = destruct_flex_t t1 in
                   let uu____18205 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18204 uu____18205
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18206;
                     FStar_Syntax_Syntax.pos = uu____18207;
                     FStar_Syntax_Syntax.vars = uu____18208;_},uu____18209),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18210;
                     FStar_Syntax_Syntax.pos = uu____18211;
                     FStar_Syntax_Syntax.vars = uu____18212;_},uu____18213))
                   ->
                   let uu____18286 = destruct_flex_t t1 in
                   let uu____18287 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18286 uu____18287
               | (FStar_Syntax_Syntax.Tm_uvar uu____18288,uu____18289) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18306 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18306 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18313;
                     FStar_Syntax_Syntax.pos = uu____18314;
                     FStar_Syntax_Syntax.vars = uu____18315;_},uu____18316),uu____18317)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18354 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18354 t2 wl
               | (uu____18361,FStar_Syntax_Syntax.Tm_uvar uu____18362) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18379,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18380;
                     FStar_Syntax_Syntax.pos = uu____18381;
                     FStar_Syntax_Syntax.vars = uu____18382;_},uu____18383))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18420,FStar_Syntax_Syntax.Tm_type uu____18421) ->
                   solve_t' env
                     (let uu___204_18439 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18439.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18439.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18439.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18439.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18439.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18439.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18439.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18439.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18439.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18440;
                     FStar_Syntax_Syntax.pos = uu____18441;
                     FStar_Syntax_Syntax.vars = uu____18442;_},uu____18443),FStar_Syntax_Syntax.Tm_type
                  uu____18444) ->
                   solve_t' env
                     (let uu___204_18482 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18482.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18482.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18482.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18482.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18482.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18482.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18482.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18482.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18482.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18483,FStar_Syntax_Syntax.Tm_arrow uu____18484) ->
                   solve_t' env
                     (let uu___204_18514 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18514.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18514.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18514.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18514.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18514.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18514.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18514.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18514.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18514.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18515;
                     FStar_Syntax_Syntax.pos = uu____18516;
                     FStar_Syntax_Syntax.vars = uu____18517;_},uu____18518),FStar_Syntax_Syntax.Tm_arrow
                  uu____18519) ->
                   solve_t' env
                     (let uu___204_18569 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18569.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18569.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18569.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18569.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18569.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18569.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18569.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18569.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18569.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18570,uu____18571) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18590 =
                        let uu____18591 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18591 in
                      if uu____18590
                      then
                        let uu____18592 =
                          FStar_All.pipe_left
                            (fun _0_72  ->
                               FStar_TypeChecker_Common.TProb _0_72)
                            (let uu___205_18598 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18598.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18598.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18598.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18598.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18598.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18598.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18598.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18598.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18598.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18599 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18592 uu____18599 t2
                          wl
                      else
                        (let uu____18607 = base_and_refinement env wl t2 in
                         match uu____18607 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18650 =
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      (let uu___206_18656 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18656.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18656.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18656.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18656.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18656.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18656.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18656.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18656.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18656.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18657 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18650
                                    uu____18657 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18677 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18677.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18677.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18680 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      uu____18680 in
                                  let guard =
                                    let uu____18692 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18692
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18700;
                     FStar_Syntax_Syntax.pos = uu____18701;
                     FStar_Syntax_Syntax.vars = uu____18702;_},uu____18703),uu____18704)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18743 =
                        let uu____18744 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18744 in
                      if uu____18743
                      then
                        let uu____18745 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___205_18751 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18751.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18751.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18751.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18751.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18751.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18751.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18751.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18751.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18751.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18752 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18745 uu____18752 t2
                          wl
                      else
                        (let uu____18760 = base_and_refinement env wl t2 in
                         match uu____18760 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18803 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___206_18809 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18809.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18809.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18809.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18809.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18809.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18809.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18809.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18809.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18809.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18810 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18803
                                    uu____18810 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18830 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18830.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18830.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18833 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____18833 in
                                  let guard =
                                    let uu____18845 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18845
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18853,FStar_Syntax_Syntax.Tm_uvar uu____18854) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18872 = base_and_refinement env wl t1 in
                      match uu____18872 with
                      | (t_base,uu____18888) ->
                          solve_t env
                            (let uu___208_18910 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_18910.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_18910.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_18910.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_18910.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_18910.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_18910.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_18910.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_18910.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18913,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18914;
                     FStar_Syntax_Syntax.pos = uu____18915;
                     FStar_Syntax_Syntax.vars = uu____18916;_},uu____18917))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18955 = base_and_refinement env wl t1 in
                      match uu____18955 with
                      | (t_base,uu____18971) ->
                          solve_t env
                            (let uu___208_18993 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_18993.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_18993.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_18993.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_18993.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_18993.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_18993.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_18993.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_18993.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18996,uu____18997) ->
                   let t21 =
                     let uu____19007 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____19007 in
                   solve_t env
                     (let uu___209_19031 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___209_19031.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___209_19031.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___209_19031.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___209_19031.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___209_19031.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___209_19031.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___209_19031.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___209_19031.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___209_19031.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____19032,FStar_Syntax_Syntax.Tm_refine uu____19033) ->
                   let t11 =
                     let uu____19043 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____19043 in
                   solve_t env
                     (let uu___210_19067 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___210_19067.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___210_19067.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___210_19067.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___210_19067.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___210_19067.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___210_19067.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___210_19067.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___210_19067.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___210_19067.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____19070,uu____19071) ->
                   let head1 =
                     let uu____19097 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19097
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19141 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19141
                       FStar_Pervasives_Native.fst in
                   let uu____19182 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19182
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19197 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19197
                      then
                        let guard =
                          let uu____19209 =
                            let uu____19210 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19210 = FStar_Syntax_Util.Equal in
                          if uu____19209
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19214 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19214) in
                        let uu____19217 = solve_prob orig guard [] wl in
                        solve env uu____19217
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19220,uu____19221) ->
                   let head1 =
                     let uu____19231 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19231
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19275 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19275
                       FStar_Pervasives_Native.fst in
                   let uu____19316 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19316
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19331 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19331
                      then
                        let guard =
                          let uu____19343 =
                            let uu____19344 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19344 = FStar_Syntax_Util.Equal in
                          if uu____19343
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19348 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19348) in
                        let uu____19351 = solve_prob orig guard [] wl in
                        solve env uu____19351
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19354,uu____19355) ->
                   let head1 =
                     let uu____19359 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19359
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19403 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19403
                       FStar_Pervasives_Native.fst in
                   let uu____19444 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19444
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19459 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19459
                      then
                        let guard =
                          let uu____19471 =
                            let uu____19472 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19472 = FStar_Syntax_Util.Equal in
                          if uu____19471
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19476 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19476) in
                        let uu____19479 = solve_prob orig guard [] wl in
                        solve env uu____19479
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19482,uu____19483) ->
                   let head1 =
                     let uu____19487 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19487
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19531 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19531
                       FStar_Pervasives_Native.fst in
                   let uu____19572 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19572
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19587 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19587
                      then
                        let guard =
                          let uu____19599 =
                            let uu____19600 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19600 = FStar_Syntax_Util.Equal in
                          if uu____19599
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19604 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19604) in
                        let uu____19607 = solve_prob orig guard [] wl in
                        solve env uu____19607
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19610,uu____19611) ->
                   let head1 =
                     let uu____19615 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19615
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19659 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19659
                       FStar_Pervasives_Native.fst in
                   let uu____19700 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19700
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19715 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19715
                      then
                        let guard =
                          let uu____19727 =
                            let uu____19728 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19728 = FStar_Syntax_Util.Equal in
                          if uu____19727
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19732 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19732) in
                        let uu____19735 = solve_prob orig guard [] wl in
                        solve env uu____19735
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19738,uu____19739) ->
                   let head1 =
                     let uu____19757 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19757
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19801 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19801
                       FStar_Pervasives_Native.fst in
                   let uu____19842 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19842
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19857 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19857
                      then
                        let guard =
                          let uu____19869 =
                            let uu____19870 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19870 = FStar_Syntax_Util.Equal in
                          if uu____19869
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19874 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19874) in
                        let uu____19877 = solve_prob orig guard [] wl in
                        solve env uu____19877
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19880,FStar_Syntax_Syntax.Tm_match uu____19881) ->
                   let head1 =
                     let uu____19907 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19907
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19951 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19951
                       FStar_Pervasives_Native.fst in
                   let uu____19992 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19992
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20007 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20007
                      then
                        let guard =
                          let uu____20019 =
                            let uu____20020 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20020 = FStar_Syntax_Util.Equal in
                          if uu____20019
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20024 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20024) in
                        let uu____20027 = solve_prob orig guard [] wl in
                        solve env uu____20027
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20030,FStar_Syntax_Syntax.Tm_uinst uu____20031) ->
                   let head1 =
                     let uu____20041 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20041
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20085 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20085
                       FStar_Pervasives_Native.fst in
                   let uu____20126 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20126
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20141 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20141
                      then
                        let guard =
                          let uu____20153 =
                            let uu____20154 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20154 = FStar_Syntax_Util.Equal in
                          if uu____20153
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20158 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20158) in
                        let uu____20161 = solve_prob orig guard [] wl in
                        solve env uu____20161
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20164,FStar_Syntax_Syntax.Tm_name uu____20165) ->
                   let head1 =
                     let uu____20169 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20169
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20213 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20213
                       FStar_Pervasives_Native.fst in
                   let uu____20254 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20254
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20269 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20269
                      then
                        let guard =
                          let uu____20281 =
                            let uu____20282 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20282 = FStar_Syntax_Util.Equal in
                          if uu____20281
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20286 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20286) in
                        let uu____20289 = solve_prob orig guard [] wl in
                        solve env uu____20289
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20292,FStar_Syntax_Syntax.Tm_constant uu____20293) ->
                   let head1 =
                     let uu____20297 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20297
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20341 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20341
                       FStar_Pervasives_Native.fst in
                   let uu____20382 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20382
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20397 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20397
                      then
                        let guard =
                          let uu____20409 =
                            let uu____20410 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20410 = FStar_Syntax_Util.Equal in
                          if uu____20409
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20414 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20414) in
                        let uu____20417 = solve_prob orig guard [] wl in
                        solve env uu____20417
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20420,FStar_Syntax_Syntax.Tm_fvar uu____20421) ->
                   let head1 =
                     let uu____20425 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20425
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20469 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20469
                       FStar_Pervasives_Native.fst in
                   let uu____20510 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20510
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20525 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20525
                      then
                        let guard =
                          let uu____20537 =
                            let uu____20538 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20538 = FStar_Syntax_Util.Equal in
                          if uu____20537
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20542 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20542) in
                        let uu____20545 = solve_prob orig guard [] wl in
                        solve env uu____20545
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20548,FStar_Syntax_Syntax.Tm_app uu____20549) ->
                   let head1 =
                     let uu____20567 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20567
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20611 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20611
                       FStar_Pervasives_Native.fst in
                   let uu____20652 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20652
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20667 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20667
                      then
                        let guard =
                          let uu____20679 =
                            let uu____20680 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20680 = FStar_Syntax_Util.Equal in
                          if uu____20679
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20684 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_Pervasives_Native.Some _0_89)
                               uu____20684) in
                        let uu____20687 = solve_prob orig guard [] wl in
                        solve env uu____20687
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20690,uu____20691) ->
                   let uu____20704 =
                     let uu____20705 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20706 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20705
                       uu____20706 in
                   failwith uu____20704
               | (FStar_Syntax_Syntax.Tm_delayed uu____20707,uu____20708) ->
                   let uu____20733 =
                     let uu____20734 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20735 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20734
                       uu____20735 in
                   failwith uu____20733
               | (uu____20736,FStar_Syntax_Syntax.Tm_delayed uu____20737) ->
                   let uu____20762 =
                     let uu____20763 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20764 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20763
                       uu____20764 in
                   failwith uu____20762
               | (uu____20765,FStar_Syntax_Syntax.Tm_let uu____20766) ->
                   let uu____20779 =
                     let uu____20780 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20781 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20780
                       uu____20781 in
                   failwith uu____20779
               | uu____20782 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20818 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20818
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20820 =
               let uu____20821 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20822 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20821 uu____20822 in
             giveup env uu____20820 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20842  ->
                    fun uu____20843  ->
                      match (uu____20842, uu____20843) with
                      | ((a1,uu____20861),(a2,uu____20863)) ->
                          let uu____20872 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_90  ->
                               FStar_TypeChecker_Common.TProb _0_90)
                            uu____20872)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20882 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20882 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20906 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20913)::[] -> wp1
              | uu____20930 ->
                  let uu____20939 =
                    let uu____20940 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20940 in
                  failwith uu____20939 in
            let uu____20943 =
              let uu____20952 =
                let uu____20953 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20953 in
              [uu____20952] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20943;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20954 = lift_c1 () in solve_eq uu____20954 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___164_20960  ->
                       match uu___164_20960 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20961 -> false)) in
             let uu____20962 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20996)::uu____20997,(wp2,uu____20999)::uu____21000)
                   -> (wp1, wp2)
               | uu____21057 ->
                   let uu____21078 =
                     let uu____21079 =
                       let uu____21084 =
                         let uu____21085 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____21086 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____21085 uu____21086 in
                       (uu____21084, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____21079 in
                   FStar_Exn.raise uu____21078 in
             match uu____20962 with
             | (wpc1,wpc2) ->
                 let uu____21105 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____21105
                 then
                   let uu____21108 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____21108 wl
                 else
                   (let uu____21112 =
                      let uu____21119 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____21119 in
                    match uu____21112 with
                    | (c2_decl,qualifiers) ->
                        let uu____21140 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21140
                        then
                          let c1_repr =
                            let uu____21144 =
                              let uu____21145 =
                                let uu____21146 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21146 in
                              let uu____21147 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21145 uu____21147 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21144 in
                          let c2_repr =
                            let uu____21149 =
                              let uu____21150 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21151 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21150 uu____21151 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21149 in
                          let prob =
                            let uu____21153 =
                              let uu____21158 =
                                let uu____21159 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21160 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21159
                                  uu____21160 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21158 in
                            FStar_TypeChecker_Common.TProb uu____21153 in
                          let wl1 =
                            let uu____21162 =
                              let uu____21165 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21165 in
                            solve_prob orig uu____21162 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21174 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21174
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____21176 =
                                     let uu____21179 =
                                       let uu____21180 =
                                         let uu____21195 =
                                           let uu____21196 =
                                             let uu____21197 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____21197] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____21196 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21198 =
                                           let uu____21201 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21202 =
                                             let uu____21205 =
                                               let uu____21206 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21206 in
                                             [uu____21205] in
                                           uu____21201 :: uu____21202 in
                                         (uu____21195, uu____21198) in
                                       FStar_Syntax_Syntax.Tm_app uu____21180 in
                                     FStar_Syntax_Syntax.mk uu____21179 in
                                   uu____21176 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____21213 =
                                    let uu____21216 =
                                      let uu____21217 =
                                        let uu____21232 =
                                          let uu____21233 =
                                            let uu____21234 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____21234] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____21233 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21235 =
                                          let uu____21238 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21239 =
                                            let uu____21242 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21243 =
                                              let uu____21246 =
                                                let uu____21247 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21247 in
                                              [uu____21246] in
                                            uu____21242 :: uu____21243 in
                                          uu____21238 :: uu____21239 in
                                        (uu____21232, uu____21235) in
                                      FStar_Syntax_Syntax.Tm_app uu____21217 in
                                    FStar_Syntax_Syntax.mk uu____21216 in
                                  uu____21213 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21254 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_91  ->
                                  FStar_TypeChecker_Common.TProb _0_91)
                               uu____21254 in
                           let wl1 =
                             let uu____21264 =
                               let uu____21267 =
                                 let uu____21270 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21270 g in
                               FStar_All.pipe_left
                                 (fun _0_92  ->
                                    FStar_Pervasives_Native.Some _0_92)
                                 uu____21267 in
                             solve_prob orig uu____21264 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21283 = FStar_Util.physical_equality c1 c2 in
        if uu____21283
        then
          let uu____21284 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21284
        else
          ((let uu____21287 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21287
            then
              let uu____21288 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21289 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21288
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21289
            else ());
           (let uu____21291 =
              let uu____21296 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21297 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21296, uu____21297) in
            match uu____21291 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21301),FStar_Syntax_Syntax.Total
                    (t2,uu____21303)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21320 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21320 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21323,FStar_Syntax_Syntax.Total uu____21324) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21342),FStar_Syntax_Syntax.Total
                    (t2,uu____21344)) ->
                     let uu____21361 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21361 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21365),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21367)) ->
                     let uu____21384 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21384 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21388),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21390)) ->
                     let uu____21407 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21407 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21410,FStar_Syntax_Syntax.Comp uu____21411) ->
                     let uu____21420 =
                       let uu___211_21425 = problem in
                       let uu____21430 =
                         let uu____21431 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21431 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21425.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21430;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21425.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21425.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21425.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21425.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21425.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21425.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21425.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21425.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21420 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21432,FStar_Syntax_Syntax.Comp uu____21433) ->
                     let uu____21442 =
                       let uu___211_21447 = problem in
                       let uu____21452 =
                         let uu____21453 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21453 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21447.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21452;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21447.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21447.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21447.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21447.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21447.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21447.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21447.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21447.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21442 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21454,FStar_Syntax_Syntax.GTotal uu____21455) ->
                     let uu____21464 =
                       let uu___212_21469 = problem in
                       let uu____21474 =
                         let uu____21475 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21475 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21469.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21469.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21469.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21474;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21469.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21469.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21469.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21469.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21469.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21469.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21464 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21476,FStar_Syntax_Syntax.Total uu____21477) ->
                     let uu____21486 =
                       let uu___212_21491 = problem in
                       let uu____21496 =
                         let uu____21497 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21497 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21491.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21491.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21491.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21496;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21491.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21491.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21491.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21491.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21491.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21491.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21486 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21498,FStar_Syntax_Syntax.Comp uu____21499) ->
                     let uu____21500 =
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
                     if uu____21500
                     then
                       let uu____21501 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21501 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21507 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21517 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21518 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21517, uu____21518)) in
                          match uu____21507 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21525 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21525
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21527 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21527 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21530 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21532 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21532) in
                                if uu____21530
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
                                  (let uu____21535 =
                                     let uu____21536 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21537 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21536 uu____21537 in
                                   giveup env uu____21535 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21543 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21581  ->
              match uu____21581 with
              | (uu____21594,uu____21595,u,uu____21597,uu____21598,uu____21599)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21543 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21631 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21631 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21649 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21677  ->
                match uu____21677 with
                | (u1,u2) ->
                    let uu____21684 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21685 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21684 uu____21685)) in
      FStar_All.pipe_right uu____21649 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21704,[])) -> "{}"
      | uu____21729 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21746 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21746
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21749 =
              FStar_List.map
                (fun uu____21759  ->
                   match uu____21759 with
                   | (uu____21764,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21749 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21769 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21769 imps
let new_t_problem:
  'Auu____21784 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21784 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21784)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21818 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21818
                then
                  let uu____21819 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21820 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21819
                    (rel_to_string rel) uu____21820
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
            let uu____21848 =
              let uu____21851 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21851 in
            FStar_Syntax_Syntax.new_bv uu____21848 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21860 =
              let uu____21863 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_94  -> FStar_Pervasives_Native.Some _0_94)
                uu____21863 in
            let uu____21866 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21860 uu____21866 in
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
          let uu____21899 = FStar_Options.eager_inference () in
          if uu____21899
          then
            let uu___213_21900 = probs in
            {
              attempting = (uu___213_21900.attempting);
              wl_deferred = (uu___213_21900.wl_deferred);
              ctr = (uu___213_21900.ctr);
              defer_ok = false;
              smt_ok = (uu___213_21900.smt_ok);
              tcenv = (uu___213_21900.tcenv)
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
             (let uu____21912 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21912
              then
                let uu____21913 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21913
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
          ((let uu____21925 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21925
            then
              let uu____21926 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21926
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21930 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21930
             then
               let uu____21931 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21931
             else ());
            (let f2 =
               let uu____21934 =
                 let uu____21935 = FStar_Syntax_Util.unmeta f1 in
                 uu____21935.FStar_Syntax_Syntax.n in
               match uu____21934 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21939 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___214_21940 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___214_21940.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___214_21940.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___214_21940.FStar_TypeChecker_Env.implicits)
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
            let uu____21962 =
              let uu____21963 =
                let uu____21964 =
                  let uu____21965 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21965
                    (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21964;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21963 in
            FStar_All.pipe_left
              (fun _0_96  -> FStar_Pervasives_Native.Some _0_96) uu____21962
let with_guard_no_simp:
  'Auu____21996 .
    'Auu____21996 ->
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
            let uu____22016 =
              let uu____22017 =
                let uu____22018 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____22018
                  (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97) in
              {
                FStar_TypeChecker_Env.guard_f = uu____22017;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____22016
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
          (let uu____22060 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22060
           then
             let uu____22061 = FStar_Syntax_Print.term_to_string t1 in
             let uu____22062 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22061
               uu____22062
           else ());
          (let prob =
             let uu____22065 =
               let uu____22070 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22070 in
             FStar_All.pipe_left
               (fun _0_98  -> FStar_TypeChecker_Common.TProb _0_98)
               uu____22065 in
           let g =
             let uu____22078 =
               let uu____22081 = singleton' env prob smt_ok in
               solve_and_commit env uu____22081
                 (fun uu____22083  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____22078 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22104 = try_teq true env t1 t2 in
        match uu____22104 with
        | FStar_Pervasives_Native.None  ->
            let uu____22107 =
              let uu____22108 =
                let uu____22113 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____22114 = FStar_TypeChecker_Env.get_range env in
                (uu____22113, uu____22114) in
              FStar_Errors.Error uu____22108 in
            FStar_Exn.raise uu____22107
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22117 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____22117
              then
                let uu____22118 = FStar_Syntax_Print.term_to_string t1 in
                let uu____22119 = FStar_Syntax_Print.term_to_string t2 in
                let uu____22120 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22118
                  uu____22119 uu____22120
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
          (let uu____22141 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22141
           then
             let uu____22142 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____22143 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____22142
               uu____22143
           else ());
          (let uu____22145 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____22145 with
           | (prob,x) ->
               let g =
                 let uu____22157 =
                   let uu____22160 = singleton' env prob smt_ok in
                   solve_and_commit env uu____22160
                     (fun uu____22162  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____22157 in
               ((let uu____22172 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____22172
                 then
                   let uu____22173 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____22174 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____22175 =
                     let uu____22176 = FStar_Util.must g in
                     guard_to_string env uu____22176 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____22173 uu____22174 uu____22175
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
          let uu____22208 = FStar_TypeChecker_Env.get_range env in
          let uu____22209 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____22208 uu____22209
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22225 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22225
         then
           let uu____22226 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22227 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22226
             uu____22227
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22232 =
             let uu____22237 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22237 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_99  -> FStar_TypeChecker_Common.CProb _0_99) uu____22232 in
         let uu____22242 =
           let uu____22245 = singleton env prob in
           solve_and_commit env uu____22245
             (fun uu____22247  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22242)
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
      fun uu____22279  ->
        match uu____22279 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22318 =
                 let uu____22319 =
                   let uu____22324 =
                     let uu____22325 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22326 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22325 uu____22326 in
                   let uu____22327 = FStar_TypeChecker_Env.get_range env in
                   (uu____22324, uu____22327) in
                 FStar_Errors.Error uu____22319 in
               FStar_Exn.raise uu____22318) in
            let equiv1 v1 v' =
              let uu____22335 =
                let uu____22340 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22341 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22340, uu____22341) in
              match uu____22335 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22360 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22390 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22390 with
                      | FStar_Syntax_Syntax.U_unif uu____22397 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22426  ->
                                    match uu____22426 with
                                    | (u,v') ->
                                        let uu____22435 = equiv1 v1 v' in
                                        if uu____22435
                                        then
                                          let uu____22438 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22438 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22454 -> [])) in
            let uu____22459 =
              let wl =
                let uu___215_22463 = empty_worklist env in
                {
                  attempting = (uu___215_22463.attempting);
                  wl_deferred = (uu___215_22463.wl_deferred);
                  ctr = (uu___215_22463.ctr);
                  defer_ok = false;
                  smt_ok = (uu___215_22463.smt_ok);
                  tcenv = (uu___215_22463.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22481  ->
                      match uu____22481 with
                      | (lb,v1) ->
                          let uu____22488 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22488 with
                           | USolved wl1 -> ()
                           | uu____22490 -> fail lb v1))) in
            let rec check_ineq uu____22498 =
              match uu____22498 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22507) -> true
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
                      uu____22530,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22532,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22543) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22550,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22558 -> false) in
            let uu____22563 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22578  ->
                      match uu____22578 with
                      | (u,v1) ->
                          let uu____22585 = check_ineq (u, v1) in
                          if uu____22585
                          then true
                          else
                            ((let uu____22588 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22588
                              then
                                let uu____22589 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22590 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22589
                                  uu____22590
                              else ());
                             false))) in
            if uu____22563
            then ()
            else
              ((let uu____22594 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22594
                then
                  ((let uu____22596 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22596);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22606 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22606))
                else ());
               (let uu____22616 =
                  let uu____22617 =
                    let uu____22622 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22622) in
                  FStar_Errors.Error uu____22617 in
                FStar_Exn.raise uu____22616))
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
      let fail uu____22674 =
        match uu____22674 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22688 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22688
       then
         let uu____22689 = wl_to_string wl in
         let uu____22690 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22689 uu____22690
       else ());
      (let g1 =
         let uu____22705 = solve_and_commit env wl fail in
         match uu____22705 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___216_22718 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___216_22718.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___216_22718.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___216_22718.FStar_TypeChecker_Env.implicits)
             }
         | uu____22723 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___217_22727 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___217_22727.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___217_22727.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___217_22727.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22750 = FStar_ST.op_Bang last_proof_ns in
    match uu____22750 with
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
            let uu___218_22937 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___218_22937.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___218_22937.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___218_22937.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22938 =
            let uu____22939 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22939 in
          if uu____22938
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22947 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22947
                   then
                     let uu____22948 = FStar_TypeChecker_Env.get_range env in
                     let uu____22949 =
                       let uu____22950 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22950 in
                     FStar_Errors.diag uu____22948 uu____22949
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22953 = check_trivial vc1 in
                   match uu____22953 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22960 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22960
                           then
                             let uu____22961 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22962 =
                               let uu____22963 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22963 in
                             FStar_Errors.diag uu____22961 uu____22962
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22968 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22968
                           then
                             let uu____22969 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22970 =
                               let uu____22971 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22971 in
                             FStar_Errors.diag uu____22969 uu____22970
                           else ());
                          (let vcs =
                             let uu____22982 = FStar_Options.use_tactics () in
                             if uu____22982
                             then
                               FStar_Options.with_saved_options
                                 (fun uu____23001  ->
                                    (let uu____23003 =
                                       FStar_Options.set_options
                                         FStar_Options.Set "--no_tactics" in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____23003);
                                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                      env vc2)
                             else
                               (let uu____23005 =
                                  let uu____23012 = FStar_Options.peek () in
                                  (env, vc2, uu____23012) in
                                [uu____23005]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____23046  ->
                                   match uu____23046 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____23057 = check_trivial goal1 in
                                       (match uu____23057 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____23059 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____23059
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____23066 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____23066
                                              then
                                                let uu____23067 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____23068 =
                                                  let uu____23069 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____23070 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____23069 uu____23070 in
                                                FStar_Errors.diag uu____23067
                                                  uu____23068
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
      let uu____23082 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23082 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23088 =
            let uu____23089 =
              let uu____23094 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____23094) in
            FStar_Errors.Error uu____23089 in
          FStar_Exn.raise uu____23088
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____23103 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____23103 with
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
          let uu____23125 = FStar_Syntax_Unionfind.find u in
          match uu____23125 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23128 -> false in
        let rec until_fixpoint acc implicits =
          let uu____23146 = acc in
          match uu____23146 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23232 = hd1 in
                   (match uu____23232 with
                    | (uu____23245,env,u,tm,k,r) ->
                        let uu____23251 = unresolved u in
                        if uu____23251
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____23282 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23282
                            then
                              let uu____23283 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23284 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23285 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23283 uu____23284 uu____23285
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___219_23288 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___219_23288.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___219_23288.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___219_23288.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___219_23288.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___219_23288.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___219_23288.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___219_23288.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___219_23288.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___219_23288.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___219_23288.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___219_23288.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___219_23288.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___219_23288.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___219_23288.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___219_23288.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___219_23288.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___219_23288.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___219_23288.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___219_23288.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___219_23288.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___219_23288.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___219_23288.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___219_23288.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___219_23288.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___219_23288.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___219_23288.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___219_23288.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___219_23288.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___219_23288.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___219_23288.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___219_23288.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___219_23288.FStar_TypeChecker_Env.dsenv)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____23291 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___220_23299 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___220_23299.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___220_23299.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___220_23299.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___220_23299.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___220_23299.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___220_23299.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___220_23299.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___220_23299.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___220_23299.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___220_23299.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___220_23299.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___220_23299.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___220_23299.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___220_23299.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___220_23299.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___220_23299.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___220_23299.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___220_23299.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___220_23299.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___220_23299.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___220_23299.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___220_23299.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___220_23299.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___220_23299.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___220_23299.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___220_23299.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___220_23299.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___220_23299.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___220_23299.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___220_23299.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___220_23299.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___220_23299.FStar_TypeChecker_Env.dsenv)
                                     }) tm1 in
                                match uu____23291 with
                                | (uu____23300,uu____23301,g1) -> g1
                              else
                                (let uu____23304 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___221_23312 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___221_23312.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___221_23312.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___221_23312.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___221_23312.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___221_23312.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___221_23312.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___221_23312.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___221_23312.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___221_23312.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___221_23312.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___221_23312.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___221_23312.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___221_23312.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___221_23312.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___221_23312.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___221_23312.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___221_23312.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___221_23312.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___221_23312.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___221_23312.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___221_23312.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___221_23312.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___221_23312.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___221_23312.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___221_23312.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___221_23312.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___221_23312.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___221_23312.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___221_23312.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___221_23312.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___221_23312.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___221_23312.FStar_TypeChecker_Env.dsenv)
                                      }) tm1 in
                                 match uu____23304 with
                                 | (uu____23313,uu____23314,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___222_23317 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___222_23317.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___222_23317.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___222_23317.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23320 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23326  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23320 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___223_23354 = g in
        let uu____23355 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___223_23354.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___223_23354.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___223_23354.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23355
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
        let uu____23413 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23413 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23426 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23426
      | (reason,uu____23428,uu____23429,e,t,r)::uu____23433 ->
          let uu____23460 =
            let uu____23461 =
              let uu____23466 =
                let uu____23467 = FStar_Syntax_Print.term_to_string t in
                let uu____23468 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23467 uu____23468 in
              (uu____23466, r) in
            FStar_Errors.Error uu____23461 in
          FStar_Exn.raise uu____23460
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___224_23477 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___224_23477.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___224_23477.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___224_23477.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23506 = try_teq false env t1 t2 in
        match uu____23506 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23510 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23510 with
             | FStar_Pervasives_Native.Some uu____23515 -> true
             | FStar_Pervasives_Native.None  -> false)