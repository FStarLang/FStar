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
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12110;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12111;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12114;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12115;
                           FStar_Syntax_Syntax.fv_qual = uu____12116;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12120,uu____12121) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12163) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12169) ->
                         may_relate t
                     | uu____12174 -> false in
                   let uu____12175 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12175
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
                                let uu____12192 =
                                  let uu____12193 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12193 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12192 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12195 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12195
                   else
                     (let uu____12197 =
                        let uu____12198 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12199 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12198 uu____12199 in
                      giveup env1 uu____12197 orig)
               | (uu____12200,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___195_12214 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___195_12214.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___195_12214.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___195_12214.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___195_12214.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___195_12214.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___195_12214.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___195_12214.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___195_12214.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12215,FStar_Pervasives_Native.None ) ->
                   ((let uu____12227 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12227
                     then
                       let uu____12228 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12229 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12230 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12231 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12228
                         uu____12229 uu____12230 uu____12231
                     else ());
                    (let uu____12233 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12233 with
                     | (head11,args1) ->
                         let uu____12270 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12270 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12324 =
                                  let uu____12325 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12326 = args_to_string args1 in
                                  let uu____12327 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12328 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12325 uu____12326 uu____12327
                                    uu____12328 in
                                giveup env1 uu____12324 orig
                              else
                                (let uu____12330 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12336 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12336 = FStar_Syntax_Util.Equal) in
                                 if uu____12330
                                 then
                                   let uu____12337 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12337 with
                                   | USolved wl2 ->
                                       let uu____12339 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12339
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12343 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12343 with
                                    | (base1,refinement1) ->
                                        let uu____12380 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12380 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12461 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12461 with
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
                                                           (fun uu____12483 
                                                              ->
                                                              fun uu____12484
                                                                 ->
                                                                match 
                                                                  (uu____12483,
                                                                    uu____12484)
                                                                with
                                                                | ((a,uu____12502),
                                                                   (a',uu____12504))
                                                                    ->
                                                                    let uu____12513
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
                                                                    uu____12513)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12523 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12523 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12529 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___196_12577 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___196_12577.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12616 =
          match uu____12616 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12832  ->
                              match uu____12832 with
                              | (x,imp) ->
                                  let uu____12843 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12843, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12856 = FStar_Syntax_Util.type_u () in
                      match uu____12856 with
                      | (t1,uu____12862) ->
                          let uu____12863 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12863 in
                    let uu____12868 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12868 with
                     | (t',tm_u1) ->
                         let uu____12881 = destruct_flex_t t' in
                         (match uu____12881 with
                          | (uu____12918,u1,k1,uu____12921) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12980 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12980 in
                              let sol =
                                let uu____12984 =
                                  let uu____12993 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12993) in
                                TERM uu____12984 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13129 = pat_var_opt env pat_args hd1 in
                    (match uu____13129 with
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
                                    (fun uu____13192  ->
                                       match uu____13192 with
                                       | (x,uu____13198) ->
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
                            let uu____13213 =
                              let uu____13214 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____13214 in
                            if uu____13213
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____13226 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____13226 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____13241::uu____13242) ->
                    let uu____13273 =
                      let uu____13286 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13286 in
                    (match uu____13273 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13325 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13332::uu____13333,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13368 =
                let uu____13381 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13381 in
              (match uu____13368 with
               | (all_formals,res_t) ->
                   let uu____13406 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13406 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13440 = lhs in
          match uu____13440 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13450 ->
                    let uu____13451 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13451 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13480 = p in
          match uu____13480 with
          | (((u,k),xs,c),ps,(h,uu____13491,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13573 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13573 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13596 = h gs_xs in
                     let uu____13597 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59) in
                     FStar_Syntax_Util.abs xs1 uu____13596 uu____13597 in
                   ((let uu____13603 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13603
                     then
                       let uu____13604 =
                         let uu____13607 =
                           let uu____13608 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13608
                             (FStar_String.concat "\n\t") in
                         let uu____13613 =
                           let uu____13616 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13617 =
                             let uu____13620 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13621 =
                               let uu____13624 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13625 =
                                 let uu____13628 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13629 =
                                   let uu____13632 =
                                     let uu____13633 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13633
                                       (FStar_String.concat ", ") in
                                   let uu____13638 =
                                     let uu____13641 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13641] in
                                   uu____13632 :: uu____13638 in
                                 uu____13628 :: uu____13629 in
                               uu____13624 :: uu____13625 in
                             uu____13620 :: uu____13621 in
                           uu____13616 :: uu____13617 in
                         uu____13607 :: uu____13613 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13604
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___161_13662 =
          match uu___161_13662 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13694 = p in
          match uu____13694 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13785 = FStar_List.nth ps i in
              (match uu____13785 with
               | (pi,uu____13789) ->
                   let uu____13794 = FStar_List.nth xs i in
                   (match uu____13794 with
                    | (xi,uu____13806) ->
                        let rec gs k =
                          let uu____13819 =
                            let uu____13832 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13832 in
                          match uu____13819 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13907)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13920 = new_uvar r xs k_a in
                                    (match uu____13920 with
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
                                         let uu____13942 = aux subst2 tl1 in
                                         (match uu____13942 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13969 =
                                                let uu____13972 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13972 :: gi_xs' in
                                              let uu____13973 =
                                                let uu____13976 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13976 :: gi_ps' in
                                              (uu____13969, uu____13973))) in
                              aux [] bs in
                        let uu____13981 =
                          let uu____13982 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13982 in
                        if uu____13981
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13986 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13986 with
                           | (g_xs,uu____13998) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____14009 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____14010 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_60  ->
                                        FStar_Pervasives_Native.Some _0_60) in
                                 FStar_Syntax_Util.abs xs uu____14009
                                   uu____14010 in
                               let sub1 =
                                 let uu____14016 =
                                   let uu____14021 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____14024 =
                                     let uu____14027 =
                                       FStar_List.map
                                         (fun uu____14042  ->
                                            match uu____14042 with
                                            | (uu____14051,uu____14052,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____14027 in
                                   mk_problem (p_scope orig) orig uu____14021
                                     (p_rel orig) uu____14024
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____14016 in
                               ((let uu____14067 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14067
                                 then
                                   let uu____14068 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____14069 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14068 uu____14069
                                 else ());
                                (let wl2 =
                                   let uu____14072 =
                                     let uu____14075 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____14075 in
                                   solve_prob orig uu____14072
                                     [TERM (u, proj)] wl1 in
                                 let uu____14084 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____14084))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14115 = lhs in
          match uu____14115 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14151 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14151 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14184 =
                        let uu____14231 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14231) in
                      FStar_Pervasives_Native.Some uu____14184
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14375 =
                           let uu____14382 =
                             let uu____14383 = FStar_Syntax_Subst.compress k1 in
                             uu____14383.FStar_Syntax_Syntax.n in
                           (uu____14382, args) in
                         match uu____14375 with
                         | (uu____14394,[]) ->
                             let uu____14397 =
                               let uu____14408 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14408) in
                             FStar_Pervasives_Native.Some uu____14397
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14429,uu____14430) ->
                             let uu____14451 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14451 with
                              | (uv1,uv_args) ->
                                  let uu____14494 =
                                    let uu____14495 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14495.FStar_Syntax_Syntax.n in
                                  (match uu____14494 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14505) ->
                                       let uu____14530 =
                                         pat_vars env [] uv_args in
                                       (match uu____14530 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14557  ->
                                                      let uu____14558 =
                                                        let uu____14559 =
                                                          let uu____14560 =
                                                            let uu____14565 =
                                                              let uu____14566
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14566
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14565 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14560 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14559 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14558)) in
                                            let c1 =
                                              let uu____14576 =
                                                let uu____14577 =
                                                  let uu____14582 =
                                                    let uu____14583 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14583
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14582 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14577 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14576 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14596 =
                                                let uu____14599 =
                                                  let uu____14600 =
                                                    let uu____14603 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14603
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14600 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14599 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14596 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14621 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14626,uu____14627) ->
                             let uu____14646 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14646 with
                              | (uv1,uv_args) ->
                                  let uu____14689 =
                                    let uu____14690 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14690.FStar_Syntax_Syntax.n in
                                  (match uu____14689 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14700) ->
                                       let uu____14725 =
                                         pat_vars env [] uv_args in
                                       (match uu____14725 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14752  ->
                                                      let uu____14753 =
                                                        let uu____14754 =
                                                          let uu____14755 =
                                                            let uu____14760 =
                                                              let uu____14761
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14761
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14760 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14755 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14754 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14753)) in
                                            let c1 =
                                              let uu____14771 =
                                                let uu____14772 =
                                                  let uu____14777 =
                                                    let uu____14778 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14778
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14777 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14772 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14771 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14791 =
                                                let uu____14794 =
                                                  let uu____14795 =
                                                    let uu____14798 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14798
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14795 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14794 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14791 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14816 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14823) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14864 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14864
                                 (fun _0_63  ->
                                    FStar_Pervasives_Native.Some _0_63)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14900 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14900 with
                                  | (args1,rest) ->
                                      let uu____14929 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14929 with
                                       | (xs2,c2) ->
                                           let uu____14942 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14942
                                             (fun uu____14966  ->
                                                match uu____14966 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____15006 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____15006 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____15074 =
                                        let uu____15079 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15079 in
                                      FStar_All.pipe_right uu____15074
                                        (fun _0_64  ->
                                           FStar_Pervasives_Native.Some _0_64))
                         | uu____15094 ->
                             let uu____15101 =
                               let uu____15102 =
                                 let uu____15107 =
                                   let uu____15108 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____15109 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____15110 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____15108 uu____15109 uu____15110 in
                                 (uu____15107, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____15102 in
                             FStar_Exn.raise uu____15101 in
                       let uu____15117 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15117
                         (fun uu____15172  ->
                            match uu____15172 with
                            | (xs1,c1) ->
                                let uu____15221 =
                                  let uu____15262 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15262) in
                                FStar_Pervasives_Native.Some uu____15221)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15383 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15399 = project orig env wl1 i st in
                     match uu____15399 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15413) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15428 = imitate orig env wl1 st in
                  match uu____15428 with
                  | Failed uu____15433 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15464 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15464 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15489 =
                      let uu____15490 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15490 wl2 in
                    (match uu____15489 with
                     | Failed uu____15491 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15509 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15509 with
                | (hd1,uu____15525) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15546 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15559 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15560 -> true
                     | uu____15577 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15581 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15581
                         then true
                         else
                           ((let uu____15584 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15584
                             then
                               let uu____15585 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15585
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15605 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15605 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15618 =
                            let uu____15619 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15619 in
                          giveup_or_defer1 orig uu____15618
                        else
                          (let uu____15621 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15621
                           then
                             let uu____15622 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15622
                              then
                                let uu____15623 = subterms args_lhs in
                                imitate' orig env wl1 uu____15623
                              else
                                ((let uu____15628 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15628
                                  then
                                    let uu____15629 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15630 = names_to_string fvs1 in
                                    let uu____15631 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15629 uu____15630 uu____15631
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
                               (let uu____15635 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15635
                                then
                                  ((let uu____15637 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15637
                                    then
                                      let uu____15638 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15639 = names_to_string fvs1 in
                                      let uu____15640 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15638 uu____15639 uu____15640
                                    else ());
                                   (let uu____15642 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15642))
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
                     (let uu____15653 =
                        let uu____15654 = FStar_Syntax_Free.names t1 in
                        check_head uu____15654 t2 in
                      if uu____15653
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15665 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15665
                          then
                            let uu____15666 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15667 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15666 uu____15667
                          else ());
                         (let uu____15675 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15675))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15752 uu____15753 r =
               match (uu____15752, uu____15753) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15951 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15951
                   then
                     let uu____15952 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15952
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15976 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15976
                       then
                         let uu____15977 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15978 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15979 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15980 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15981 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15977 uu____15978 uu____15979 uu____15980
                           uu____15981
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____16041 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____16041 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16055 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____16055 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16109 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16109 in
                                  let uu____16112 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16112 k3)
                           else
                             (let uu____16116 =
                                let uu____16117 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16118 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16119 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16117 uu____16118 uu____16119 in
                              failwith uu____16116) in
                       let uu____16120 =
                         let uu____16127 =
                           let uu____16140 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16140 in
                         match uu____16127 with
                         | (bs,k1') ->
                             let uu____16165 =
                               let uu____16178 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16178 in
                             (match uu____16165 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16206 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      uu____16206 in
                                  let uu____16215 =
                                    let uu____16220 =
                                      let uu____16221 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16221.FStar_Syntax_Syntax.n in
                                    let uu____16224 =
                                      let uu____16225 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16225.FStar_Syntax_Syntax.n in
                                    (uu____16220, uu____16224) in
                                  (match uu____16215 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16234,uu____16235) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16238,FStar_Syntax_Syntax.Tm_type
                                      uu____16239) -> (k2'_ys, [sub_prob])
                                   | uu____16242 ->
                                       let uu____16247 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16247 with
                                        | (t,uu____16259) ->
                                            let uu____16260 = new_uvar r zs t in
                                            (match uu____16260 with
                                             | (k_zs,uu____16272) ->
                                                 let kprob =
                                                   let uu____16274 =
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
                                                          _0_66) uu____16274 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16120 with
                       | (k_u',sub_probs) ->
                           let uu____16291 =
                             let uu____16302 =
                               let uu____16303 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16303 in
                             let uu____16312 =
                               let uu____16315 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16315 in
                             let uu____16318 =
                               let uu____16321 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16321 in
                             (uu____16302, uu____16312, uu____16318) in
                           (match uu____16291 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16340 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16340 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16359 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16359
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16363 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16363 with
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
             let solve_one_pat uu____16416 uu____16417 =
               match (uu____16416, uu____16417) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16535 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16535
                     then
                       let uu____16536 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16537 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16536 uu____16537
                     else ());
                    (let uu____16539 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16539
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16558  ->
                              fun uu____16559  ->
                                match (uu____16558, uu____16559) with
                                | ((a,uu____16577),(t21,uu____16579)) ->
                                    let uu____16588 =
                                      let uu____16593 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16593
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16588
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67))
                           xs args2 in
                       let guard =
                         let uu____16599 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16599 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16614 = occurs_check env wl (u1, k1) t21 in
                        match uu____16614 with
                        | (occurs_ok,uu____16622) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16630 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16630
                            then
                              let sol =
                                let uu____16632 =
                                  let uu____16641 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16641) in
                                TERM uu____16632 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16648 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16648
                               then
                                 let uu____16649 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16649 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16673,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16699 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16699
                                       then
                                         let uu____16700 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16700
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16707 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16709 = lhs in
             match uu____16709 with
             | (t1,u1,k1,args1) ->
                 let uu____16714 = rhs in
                 (match uu____16714 with
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
                       | uu____16754 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16764 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16764 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16782) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16789 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16789
                                    then
                                      let uu____16790 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16790
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16797 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16799 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16799
        then
          let uu____16800 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16800
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16804 = FStar_Util.physical_equality t1 t2 in
           if uu____16804
           then
             let uu____16805 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16805
           else
             ((let uu____16808 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16808
               then
                 let uu____16809 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16809
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16812,uu____16813) ->
                   let uu____16840 =
                     let uu___197_16841 = problem in
                     let uu____16842 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16841.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16842;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16841.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16841.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16841.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16841.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16841.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16841.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16841.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16841.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16840 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16843,uu____16844) ->
                   let uu____16851 =
                     let uu___197_16852 = problem in
                     let uu____16853 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16852.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16853;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16852.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16852.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16852.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16852.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16852.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16852.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16852.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16852.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16851 wl
               | (uu____16854,FStar_Syntax_Syntax.Tm_ascribed uu____16855) ->
                   let uu____16882 =
                     let uu___198_16883 = problem in
                     let uu____16884 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16883.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16883.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16883.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16884;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16883.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16883.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16883.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16883.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16883.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16883.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16882 wl
               | (uu____16885,FStar_Syntax_Syntax.Tm_meta uu____16886) ->
                   let uu____16893 =
                     let uu___198_16894 = problem in
                     let uu____16895 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16894.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16894.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16894.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16895;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16894.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16894.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16894.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16894.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16894.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16894.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16893 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16896,uu____16897) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16898,FStar_Syntax_Syntax.Tm_bvar uu____16899) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___162_16954 =
                     match uu___162_16954 with
                     | [] -> c
                     | bs ->
                         let uu____16976 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16976 in
                   let uu____16985 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16985 with
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
                                   let uu____17127 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17127
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17129 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.CProb _0_68)
                                   uu____17129))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___163_17205 =
                     match uu___163_17205 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17239 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17239 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17375 =
                                   let uu____17380 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17381 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17380
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17381 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17375))
               | (FStar_Syntax_Syntax.Tm_abs uu____17386,uu____17387) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17412 -> true
                     | uu____17429 -> false in
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
                       (let uu____17476 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17484 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17484.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17484.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17484.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17484.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17484.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17484.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17484.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17484.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17484.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17484.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17484.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17484.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17484.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17484.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17484.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17484.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17484.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17484.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17484.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17484.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17484.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17484.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17484.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17484.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17484.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17484.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17484.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17484.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17484.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17484.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17476 with
                        | (uu____17487,ty,uu____17489) ->
                            let uu____17490 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17490) in
                   let uu____17491 =
                     let uu____17508 = maybe_eta t1 in
                     let uu____17515 = maybe_eta t2 in
                     (uu____17508, uu____17515) in
                   (match uu____17491 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17557 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17557.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17557.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17557.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17557.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17557.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17557.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17557.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17557.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17580 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17580
                        then
                          let uu____17581 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17581 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17596 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17596.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17596.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17596.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17596.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17596.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17596.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17596.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17596.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17620 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17620
                        then
                          let uu____17621 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17621 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17636 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17636.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17636.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17636.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17636.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17636.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17636.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17636.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17636.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17640 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17657,FStar_Syntax_Syntax.Tm_abs uu____17658) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17683 -> true
                     | uu____17700 -> false in
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
                       (let uu____17747 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17755 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17755.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17755.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17755.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17755.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17755.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17755.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17755.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17755.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17755.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17755.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17755.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17755.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17755.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17755.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17755.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17755.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17755.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17755.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17755.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17755.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17755.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17755.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17755.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17755.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17755.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17755.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17755.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17755.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17755.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17755.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17747 with
                        | (uu____17758,ty,uu____17760) ->
                            let uu____17761 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17761) in
                   let uu____17762 =
                     let uu____17779 = maybe_eta t1 in
                     let uu____17786 = maybe_eta t2 in
                     (uu____17779, uu____17786) in
                   (match uu____17762 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17828 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17828.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17828.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17828.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17828.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17828.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17828.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17828.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17828.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17851 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17851
                        then
                          let uu____17852 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17852 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17867 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17867.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17867.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17867.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17867.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17867.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17867.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17867.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17867.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17891 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17891
                        then
                          let uu____17892 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17892 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17907 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17907.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17907.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17907.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17907.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17907.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17907.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17907.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17907.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17911 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17928,FStar_Syntax_Syntax.Tm_refine uu____17929) ->
                   let uu____17942 = as_refinement env wl t1 in
                   (match uu____17942 with
                    | (x1,phi1) ->
                        let uu____17949 = as_refinement env wl t2 in
                        (match uu____17949 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17957 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_70  ->
                                    FStar_TypeChecker_Common.TProb _0_70)
                                 uu____17957 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17995 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17995
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17999 =
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
                                 let uu____18005 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____18005 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____18014 =
                                   let uu____18019 =
                                     let uu____18020 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____18020 :: (p_scope orig) in
                                   mk_problem uu____18019 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.TProb _0_71)
                                   uu____18014 in
                               let uu____18025 =
                                 solve env1
                                   (let uu___202_18027 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___202_18027.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___202_18027.smt_ok);
                                      tcenv = (uu___202_18027.tcenv)
                                    }) in
                               (match uu____18025 with
                                | Failed uu____18034 -> fallback ()
                                | Success uu____18039 ->
                                    let guard =
                                      let uu____18043 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____18048 =
                                        let uu____18049 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____18049
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____18043
                                        uu____18048 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___203_18058 = wl1 in
                                      {
                                        attempting =
                                          (uu___203_18058.attempting);
                                        wl_deferred =
                                          (uu___203_18058.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___203_18058.defer_ok);
                                        smt_ok = (uu___203_18058.smt_ok);
                                        tcenv = (uu___203_18058.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18060,FStar_Syntax_Syntax.Tm_uvar uu____18061) ->
                   let uu____18094 = destruct_flex_t t1 in
                   let uu____18095 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18094 uu____18095
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18096;
                     FStar_Syntax_Syntax.pos = uu____18097;
                     FStar_Syntax_Syntax.vars = uu____18098;_},uu____18099),FStar_Syntax_Syntax.Tm_uvar
                  uu____18100) ->
                   let uu____18153 = destruct_flex_t t1 in
                   let uu____18154 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18153 uu____18154
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18155,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18156;
                     FStar_Syntax_Syntax.pos = uu____18157;
                     FStar_Syntax_Syntax.vars = uu____18158;_},uu____18159))
                   ->
                   let uu____18212 = destruct_flex_t t1 in
                   let uu____18213 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18212 uu____18213
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18214;
                     FStar_Syntax_Syntax.pos = uu____18215;
                     FStar_Syntax_Syntax.vars = uu____18216;_},uu____18217),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18218;
                     FStar_Syntax_Syntax.pos = uu____18219;
                     FStar_Syntax_Syntax.vars = uu____18220;_},uu____18221))
                   ->
                   let uu____18294 = destruct_flex_t t1 in
                   let uu____18295 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18294 uu____18295
               | (FStar_Syntax_Syntax.Tm_uvar uu____18296,uu____18297) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18314 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18314 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18321;
                     FStar_Syntax_Syntax.pos = uu____18322;
                     FStar_Syntax_Syntax.vars = uu____18323;_},uu____18324),uu____18325)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18362 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18362 t2 wl
               | (uu____18369,FStar_Syntax_Syntax.Tm_uvar uu____18370) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18387,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18388;
                     FStar_Syntax_Syntax.pos = uu____18389;
                     FStar_Syntax_Syntax.vars = uu____18390;_},uu____18391))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18428,FStar_Syntax_Syntax.Tm_type uu____18429) ->
                   solve_t' env
                     (let uu___204_18447 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18447.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18447.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18447.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18447.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18447.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18447.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18447.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18447.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18447.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18448;
                     FStar_Syntax_Syntax.pos = uu____18449;
                     FStar_Syntax_Syntax.vars = uu____18450;_},uu____18451),FStar_Syntax_Syntax.Tm_type
                  uu____18452) ->
                   solve_t' env
                     (let uu___204_18490 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18490.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18490.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18490.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18490.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18490.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18490.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18490.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18490.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18490.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18491,FStar_Syntax_Syntax.Tm_arrow uu____18492) ->
                   solve_t' env
                     (let uu___204_18522 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18522.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18522.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18522.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18522.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18522.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18522.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18522.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18522.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18522.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18523;
                     FStar_Syntax_Syntax.pos = uu____18524;
                     FStar_Syntax_Syntax.vars = uu____18525;_},uu____18526),FStar_Syntax_Syntax.Tm_arrow
                  uu____18527) ->
                   solve_t' env
                     (let uu___204_18577 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18577.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18577.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18577.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18577.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18577.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18577.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18577.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18577.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18577.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18578,uu____18579) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18598 =
                        let uu____18599 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18599 in
                      if uu____18598
                      then
                        let uu____18600 =
                          FStar_All.pipe_left
                            (fun _0_72  ->
                               FStar_TypeChecker_Common.TProb _0_72)
                            (let uu___205_18606 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18606.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18606.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18606.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18606.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18606.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18606.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18606.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18606.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18606.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18607 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18600 uu____18607 t2
                          wl
                      else
                        (let uu____18615 = base_and_refinement env wl t2 in
                         match uu____18615 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18658 =
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      (let uu___206_18664 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18664.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18664.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18664.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18664.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18664.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18664.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18664.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18664.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18664.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18665 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18658
                                    uu____18665 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18685 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18685.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18685.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18688 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      uu____18688 in
                                  let guard =
                                    let uu____18700 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18700
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18708;
                     FStar_Syntax_Syntax.pos = uu____18709;
                     FStar_Syntax_Syntax.vars = uu____18710;_},uu____18711),uu____18712)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18751 =
                        let uu____18752 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18752 in
                      if uu____18751
                      then
                        let uu____18753 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___205_18759 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18759.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18759.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18759.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18759.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18759.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18759.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18759.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18759.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18759.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18760 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18753 uu____18760 t2
                          wl
                      else
                        (let uu____18768 = base_and_refinement env wl t2 in
                         match uu____18768 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18811 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___206_18817 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18817.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18817.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18817.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18817.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18817.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18817.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18817.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18817.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18817.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18818 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18811
                                    uu____18818 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18838 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18838.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18838.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18841 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____18841 in
                                  let guard =
                                    let uu____18853 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18853
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18861,FStar_Syntax_Syntax.Tm_uvar uu____18862) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18880 = base_and_refinement env wl t1 in
                      match uu____18880 with
                      | (t_base,uu____18896) ->
                          solve_t env
                            (let uu___208_18918 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_18918.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_18918.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_18918.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_18918.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_18918.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_18918.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_18918.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_18918.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18921,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18922;
                     FStar_Syntax_Syntax.pos = uu____18923;
                     FStar_Syntax_Syntax.vars = uu____18924;_},uu____18925))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18963 = base_and_refinement env wl t1 in
                      match uu____18963 with
                      | (t_base,uu____18979) ->
                          solve_t env
                            (let uu___208_19001 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_19001.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_19001.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_19001.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_19001.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_19001.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_19001.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_19001.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_19001.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____19004,uu____19005) ->
                   let t21 =
                     let uu____19015 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____19015 in
                   solve_t env
                     (let uu___209_19039 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___209_19039.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___209_19039.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___209_19039.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___209_19039.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___209_19039.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___209_19039.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___209_19039.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___209_19039.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___209_19039.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____19040,FStar_Syntax_Syntax.Tm_refine uu____19041) ->
                   let t11 =
                     let uu____19051 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____19051 in
                   solve_t env
                     (let uu___210_19075 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___210_19075.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___210_19075.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___210_19075.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___210_19075.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___210_19075.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___210_19075.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___210_19075.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___210_19075.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___210_19075.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____19078,uu____19079) ->
                   let head1 =
                     let uu____19105 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19105
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19149 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19149
                       FStar_Pervasives_Native.fst in
                   let uu____19190 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19190
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19205 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19205
                      then
                        let guard =
                          let uu____19217 =
                            let uu____19218 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19218 = FStar_Syntax_Util.Equal in
                          if uu____19217
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19222 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19222) in
                        let uu____19225 = solve_prob orig guard [] wl in
                        solve env uu____19225
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19228,uu____19229) ->
                   let head1 =
                     let uu____19239 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19239
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19283 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19283
                       FStar_Pervasives_Native.fst in
                   let uu____19324 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19324
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19339 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19339
                      then
                        let guard =
                          let uu____19351 =
                            let uu____19352 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19352 = FStar_Syntax_Util.Equal in
                          if uu____19351
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19356 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19356) in
                        let uu____19359 = solve_prob orig guard [] wl in
                        solve env uu____19359
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19362,uu____19363) ->
                   let head1 =
                     let uu____19367 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19367
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19411 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19411
                       FStar_Pervasives_Native.fst in
                   let uu____19452 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19452
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19467 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19467
                      then
                        let guard =
                          let uu____19479 =
                            let uu____19480 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19480 = FStar_Syntax_Util.Equal in
                          if uu____19479
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19484 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19484) in
                        let uu____19487 = solve_prob orig guard [] wl in
                        solve env uu____19487
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19490,uu____19491) ->
                   let head1 =
                     let uu____19495 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19495
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19539 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19539
                       FStar_Pervasives_Native.fst in
                   let uu____19580 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19580
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19595 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19595
                      then
                        let guard =
                          let uu____19607 =
                            let uu____19608 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19608 = FStar_Syntax_Util.Equal in
                          if uu____19607
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19612 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19612) in
                        let uu____19615 = solve_prob orig guard [] wl in
                        solve env uu____19615
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19618,uu____19619) ->
                   let head1 =
                     let uu____19623 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19623
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19667 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19667
                       FStar_Pervasives_Native.fst in
                   let uu____19708 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19708
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19723 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19723
                      then
                        let guard =
                          let uu____19735 =
                            let uu____19736 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19736 = FStar_Syntax_Util.Equal in
                          if uu____19735
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19740 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19740) in
                        let uu____19743 = solve_prob orig guard [] wl in
                        solve env uu____19743
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19746,uu____19747) ->
                   let head1 =
                     let uu____19765 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19765
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19809 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19809
                       FStar_Pervasives_Native.fst in
                   let uu____19850 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19850
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19865 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19865
                      then
                        let guard =
                          let uu____19877 =
                            let uu____19878 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19878 = FStar_Syntax_Util.Equal in
                          if uu____19877
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19882 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19882) in
                        let uu____19885 = solve_prob orig guard [] wl in
                        solve env uu____19885
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19888,FStar_Syntax_Syntax.Tm_match uu____19889) ->
                   let head1 =
                     let uu____19915 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19915
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19959 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19959
                       FStar_Pervasives_Native.fst in
                   let uu____20000 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20000
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20015 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20015
                      then
                        let guard =
                          let uu____20027 =
                            let uu____20028 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20028 = FStar_Syntax_Util.Equal in
                          if uu____20027
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20032 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20032) in
                        let uu____20035 = solve_prob orig guard [] wl in
                        solve env uu____20035
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20038,FStar_Syntax_Syntax.Tm_uinst uu____20039) ->
                   let head1 =
                     let uu____20049 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20049
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20093 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20093
                       FStar_Pervasives_Native.fst in
                   let uu____20134 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20134
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20149 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20149
                      then
                        let guard =
                          let uu____20161 =
                            let uu____20162 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20162 = FStar_Syntax_Util.Equal in
                          if uu____20161
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20166 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20166) in
                        let uu____20169 = solve_prob orig guard [] wl in
                        solve env uu____20169
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20172,FStar_Syntax_Syntax.Tm_name uu____20173) ->
                   let head1 =
                     let uu____20177 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20177
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20221 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20221
                       FStar_Pervasives_Native.fst in
                   let uu____20262 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20262
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20277 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20277
                      then
                        let guard =
                          let uu____20289 =
                            let uu____20290 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20290 = FStar_Syntax_Util.Equal in
                          if uu____20289
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20294 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20294) in
                        let uu____20297 = solve_prob orig guard [] wl in
                        solve env uu____20297
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20300,FStar_Syntax_Syntax.Tm_constant uu____20301) ->
                   let head1 =
                     let uu____20305 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20305
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20349 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20349
                       FStar_Pervasives_Native.fst in
                   let uu____20390 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20390
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20405 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20405
                      then
                        let guard =
                          let uu____20417 =
                            let uu____20418 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20418 = FStar_Syntax_Util.Equal in
                          if uu____20417
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20422 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20422) in
                        let uu____20425 = solve_prob orig guard [] wl in
                        solve env uu____20425
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20428,FStar_Syntax_Syntax.Tm_fvar uu____20429) ->
                   let head1 =
                     let uu____20433 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20433
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20477 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20477
                       FStar_Pervasives_Native.fst in
                   let uu____20518 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20518
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20533 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20533
                      then
                        let guard =
                          let uu____20545 =
                            let uu____20546 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20546 = FStar_Syntax_Util.Equal in
                          if uu____20545
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20550 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20550) in
                        let uu____20553 = solve_prob orig guard [] wl in
                        solve env uu____20553
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20556,FStar_Syntax_Syntax.Tm_app uu____20557) ->
                   let head1 =
                     let uu____20575 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20575
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20619 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20619
                       FStar_Pervasives_Native.fst in
                   let uu____20660 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20660
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20675 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20675
                      then
                        let guard =
                          let uu____20687 =
                            let uu____20688 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20688 = FStar_Syntax_Util.Equal in
                          if uu____20687
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20692 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_Pervasives_Native.Some _0_89)
                               uu____20692) in
                        let uu____20695 = solve_prob orig guard [] wl in
                        solve env uu____20695
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20698,uu____20699) ->
                   let uu____20712 =
                     let uu____20713 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20714 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20713
                       uu____20714 in
                   failwith uu____20712
               | (FStar_Syntax_Syntax.Tm_delayed uu____20715,uu____20716) ->
                   let uu____20741 =
                     let uu____20742 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20743 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20742
                       uu____20743 in
                   failwith uu____20741
               | (uu____20744,FStar_Syntax_Syntax.Tm_delayed uu____20745) ->
                   let uu____20770 =
                     let uu____20771 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20772 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20771
                       uu____20772 in
                   failwith uu____20770
               | (uu____20773,FStar_Syntax_Syntax.Tm_let uu____20774) ->
                   let uu____20787 =
                     let uu____20788 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20789 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20788
                       uu____20789 in
                   failwith uu____20787
               | uu____20790 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20826 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20826
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20828 =
               let uu____20829 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20830 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20829 uu____20830 in
             giveup env uu____20828 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20850  ->
                    fun uu____20851  ->
                      match (uu____20850, uu____20851) with
                      | ((a1,uu____20869),(a2,uu____20871)) ->
                          let uu____20880 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_90  ->
                               FStar_TypeChecker_Common.TProb _0_90)
                            uu____20880)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20890 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20890 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20914 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20921)::[] -> wp1
              | uu____20938 ->
                  let uu____20947 =
                    let uu____20948 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20948 in
                  failwith uu____20947 in
            let uu____20951 =
              let uu____20960 =
                let uu____20961 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20961 in
              [uu____20960] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20951;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20962 = lift_c1 () in solve_eq uu____20962 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___164_20968  ->
                       match uu___164_20968 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20969 -> false)) in
             let uu____20970 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21004)::uu____21005,(wp2,uu____21007)::uu____21008)
                   -> (wp1, wp2)
               | uu____21065 ->
                   let uu____21086 =
                     let uu____21087 =
                       let uu____21092 =
                         let uu____21093 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____21094 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____21093 uu____21094 in
                       (uu____21092, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____21087 in
                   FStar_Exn.raise uu____21086 in
             match uu____20970 with
             | (wpc1,wpc2) ->
                 let uu____21113 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____21113
                 then
                   let uu____21116 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____21116 wl
                 else
                   (let uu____21120 =
                      let uu____21127 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____21127 in
                    match uu____21120 with
                    | (c2_decl,qualifiers) ->
                        let uu____21148 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21148
                        then
                          let c1_repr =
                            let uu____21152 =
                              let uu____21153 =
                                let uu____21154 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21154 in
                              let uu____21155 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21153 uu____21155 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21152 in
                          let c2_repr =
                            let uu____21157 =
                              let uu____21158 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21159 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21158 uu____21159 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21157 in
                          let prob =
                            let uu____21161 =
                              let uu____21166 =
                                let uu____21167 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21168 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21167
                                  uu____21168 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21166 in
                            FStar_TypeChecker_Common.TProb uu____21161 in
                          let wl1 =
                            let uu____21170 =
                              let uu____21173 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21173 in
                            solve_prob orig uu____21170 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21182 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21182
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____21184 =
                                     let uu____21187 =
                                       let uu____21188 =
                                         let uu____21203 =
                                           let uu____21204 =
                                             let uu____21205 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____21205] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____21204 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21206 =
                                           let uu____21209 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21210 =
                                             let uu____21213 =
                                               let uu____21214 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21214 in
                                             [uu____21213] in
                                           uu____21209 :: uu____21210 in
                                         (uu____21203, uu____21206) in
                                       FStar_Syntax_Syntax.Tm_app uu____21188 in
                                     FStar_Syntax_Syntax.mk uu____21187 in
                                   uu____21184 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____21221 =
                                    let uu____21224 =
                                      let uu____21225 =
                                        let uu____21240 =
                                          let uu____21241 =
                                            let uu____21242 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____21242] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____21241 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21243 =
                                          let uu____21246 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21247 =
                                            let uu____21250 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21251 =
                                              let uu____21254 =
                                                let uu____21255 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21255 in
                                              [uu____21254] in
                                            uu____21250 :: uu____21251 in
                                          uu____21246 :: uu____21247 in
                                        (uu____21240, uu____21243) in
                                      FStar_Syntax_Syntax.Tm_app uu____21225 in
                                    FStar_Syntax_Syntax.mk uu____21224 in
                                  uu____21221 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21262 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_91  ->
                                  FStar_TypeChecker_Common.TProb _0_91)
                               uu____21262 in
                           let wl1 =
                             let uu____21272 =
                               let uu____21275 =
                                 let uu____21278 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21278 g in
                               FStar_All.pipe_left
                                 (fun _0_92  ->
                                    FStar_Pervasives_Native.Some _0_92)
                                 uu____21275 in
                             solve_prob orig uu____21272 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21291 = FStar_Util.physical_equality c1 c2 in
        if uu____21291
        then
          let uu____21292 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21292
        else
          ((let uu____21295 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21295
            then
              let uu____21296 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21297 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21296
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21297
            else ());
           (let uu____21299 =
              let uu____21304 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21305 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21304, uu____21305) in
            match uu____21299 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21309),FStar_Syntax_Syntax.Total
                    (t2,uu____21311)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21328 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21328 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21331,FStar_Syntax_Syntax.Total uu____21332) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21350),FStar_Syntax_Syntax.Total
                    (t2,uu____21352)) ->
                     let uu____21369 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21369 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21373),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21375)) ->
                     let uu____21392 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21392 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21396),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21398)) ->
                     let uu____21415 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21415 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21418,FStar_Syntax_Syntax.Comp uu____21419) ->
                     let uu____21428 =
                       let uu___211_21433 = problem in
                       let uu____21438 =
                         let uu____21439 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21439 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21433.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21438;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21433.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21433.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21433.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21433.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21433.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21433.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21433.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21433.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21428 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21440,FStar_Syntax_Syntax.Comp uu____21441) ->
                     let uu____21450 =
                       let uu___211_21455 = problem in
                       let uu____21460 =
                         let uu____21461 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21461 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21455.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21460;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21455.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21455.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21455.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21455.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21455.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21455.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21455.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21455.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21450 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21462,FStar_Syntax_Syntax.GTotal uu____21463) ->
                     let uu____21472 =
                       let uu___212_21477 = problem in
                       let uu____21482 =
                         let uu____21483 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21483 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21477.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21477.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21477.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21482;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21477.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21477.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21477.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21477.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21477.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21477.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21472 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21484,FStar_Syntax_Syntax.Total uu____21485) ->
                     let uu____21494 =
                       let uu___212_21499 = problem in
                       let uu____21504 =
                         let uu____21505 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21505 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21499.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21499.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21499.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21504;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21499.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21499.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21499.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21499.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21499.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21499.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21494 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21506,FStar_Syntax_Syntax.Comp uu____21507) ->
                     let uu____21508 =
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
                     if uu____21508
                     then
                       let uu____21509 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21509 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21515 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21525 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21526 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21525, uu____21526)) in
                          match uu____21515 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21533 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21533
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21535 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21535 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21538 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21540 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21540) in
                                if uu____21538
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
                                  (let uu____21543 =
                                     let uu____21544 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21545 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21544 uu____21545 in
                                   giveup env uu____21543 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21551 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21589  ->
              match uu____21589 with
              | (uu____21602,uu____21603,u,uu____21605,uu____21606,uu____21607)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21551 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21639 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21639 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21657 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21685  ->
                match uu____21685 with
                | (u1,u2) ->
                    let uu____21692 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21693 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21692 uu____21693)) in
      FStar_All.pipe_right uu____21657 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21712,[])) -> "{}"
      | uu____21737 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21754 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21754
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21757 =
              FStar_List.map
                (fun uu____21767  ->
                   match uu____21767 with
                   | (uu____21772,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21757 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21777 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21777 imps
let new_t_problem:
  'Auu____21792 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21792 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21792)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21826 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21826
                then
                  let uu____21827 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21828 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21827
                    (rel_to_string rel) uu____21828
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
            let uu____21856 =
              let uu____21859 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21859 in
            FStar_Syntax_Syntax.new_bv uu____21856 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21868 =
              let uu____21871 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_94  -> FStar_Pervasives_Native.Some _0_94)
                uu____21871 in
            let uu____21874 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21868 uu____21874 in
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
          let uu____21907 = FStar_Options.eager_inference () in
          if uu____21907
          then
            let uu___213_21908 = probs in
            {
              attempting = (uu___213_21908.attempting);
              wl_deferred = (uu___213_21908.wl_deferred);
              ctr = (uu___213_21908.ctr);
              defer_ok = false;
              smt_ok = (uu___213_21908.smt_ok);
              tcenv = (uu___213_21908.tcenv)
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
             (let uu____21920 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21920
              then
                let uu____21921 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21921
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
          ((let uu____21933 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21933
            then
              let uu____21934 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21934
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21938 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21938
             then
               let uu____21939 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21939
             else ());
            (let f2 =
               let uu____21942 =
                 let uu____21943 = FStar_Syntax_Util.unmeta f1 in
                 uu____21943.FStar_Syntax_Syntax.n in
               match uu____21942 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21947 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___214_21948 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___214_21948.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___214_21948.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___214_21948.FStar_TypeChecker_Env.implicits)
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
            let uu____21970 =
              let uu____21971 =
                let uu____21972 =
                  let uu____21973 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21973
                    (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21972;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21971 in
            FStar_All.pipe_left
              (fun _0_96  -> FStar_Pervasives_Native.Some _0_96) uu____21970
let with_guard_no_simp:
  'Auu____22004 .
    'Auu____22004 ->
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
            let uu____22024 =
              let uu____22025 =
                let uu____22026 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____22026
                  (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97) in
              {
                FStar_TypeChecker_Env.guard_f = uu____22025;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____22024
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
          (let uu____22068 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22068
           then
             let uu____22069 = FStar_Syntax_Print.term_to_string t1 in
             let uu____22070 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22069
               uu____22070
           else ());
          (let prob =
             let uu____22073 =
               let uu____22078 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22078 in
             FStar_All.pipe_left
               (fun _0_98  -> FStar_TypeChecker_Common.TProb _0_98)
               uu____22073 in
           let g =
             let uu____22086 =
               let uu____22089 = singleton' env prob smt_ok in
               solve_and_commit env uu____22089
                 (fun uu____22091  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____22086 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22112 = try_teq true env t1 t2 in
        match uu____22112 with
        | FStar_Pervasives_Native.None  ->
            let uu____22115 =
              let uu____22116 =
                let uu____22121 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____22122 = FStar_TypeChecker_Env.get_range env in
                (uu____22121, uu____22122) in
              FStar_Errors.Error uu____22116 in
            FStar_Exn.raise uu____22115
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22125 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____22125
              then
                let uu____22126 = FStar_Syntax_Print.term_to_string t1 in
                let uu____22127 = FStar_Syntax_Print.term_to_string t2 in
                let uu____22128 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22126
                  uu____22127 uu____22128
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
          (let uu____22149 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22149
           then
             let uu____22150 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____22151 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____22150
               uu____22151
           else ());
          (let uu____22153 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____22153 with
           | (prob,x) ->
               let g =
                 let uu____22165 =
                   let uu____22168 = singleton' env prob smt_ok in
                   solve_and_commit env uu____22168
                     (fun uu____22170  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____22165 in
               ((let uu____22180 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____22180
                 then
                   let uu____22181 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____22182 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____22183 =
                     let uu____22184 = FStar_Util.must g in
                     guard_to_string env uu____22184 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____22181 uu____22182 uu____22183
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
          let uu____22216 = FStar_TypeChecker_Env.get_range env in
          let uu____22217 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____22216 uu____22217
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22233 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22233
         then
           let uu____22234 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22235 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22234
             uu____22235
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22240 =
             let uu____22245 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22245 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_99  -> FStar_TypeChecker_Common.CProb _0_99) uu____22240 in
         let uu____22250 =
           let uu____22253 = singleton env prob in
           solve_and_commit env uu____22253
             (fun uu____22255  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22250)
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
      fun uu____22287  ->
        match uu____22287 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22326 =
                 let uu____22327 =
                   let uu____22332 =
                     let uu____22333 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22334 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22333 uu____22334 in
                   let uu____22335 = FStar_TypeChecker_Env.get_range env in
                   (uu____22332, uu____22335) in
                 FStar_Errors.Error uu____22327 in
               FStar_Exn.raise uu____22326) in
            let equiv1 v1 v' =
              let uu____22343 =
                let uu____22348 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22349 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22348, uu____22349) in
              match uu____22343 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22368 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22398 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22398 with
                      | FStar_Syntax_Syntax.U_unif uu____22405 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22434  ->
                                    match uu____22434 with
                                    | (u,v') ->
                                        let uu____22443 = equiv1 v1 v' in
                                        if uu____22443
                                        then
                                          let uu____22446 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22446 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22462 -> [])) in
            let uu____22467 =
              let wl =
                let uu___215_22471 = empty_worklist env in
                {
                  attempting = (uu___215_22471.attempting);
                  wl_deferred = (uu___215_22471.wl_deferred);
                  ctr = (uu___215_22471.ctr);
                  defer_ok = false;
                  smt_ok = (uu___215_22471.smt_ok);
                  tcenv = (uu___215_22471.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22489  ->
                      match uu____22489 with
                      | (lb,v1) ->
                          let uu____22496 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22496 with
                           | USolved wl1 -> ()
                           | uu____22498 -> fail lb v1))) in
            let rec check_ineq uu____22506 =
              match uu____22506 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22515) -> true
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
                      uu____22538,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22540,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22551) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22558,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22566 -> false) in
            let uu____22571 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22586  ->
                      match uu____22586 with
                      | (u,v1) ->
                          let uu____22593 = check_ineq (u, v1) in
                          if uu____22593
                          then true
                          else
                            ((let uu____22596 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22596
                              then
                                let uu____22597 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22598 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22597
                                  uu____22598
                              else ());
                             false))) in
            if uu____22571
            then ()
            else
              ((let uu____22602 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22602
                then
                  ((let uu____22604 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22604);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22614 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22614))
                else ());
               (let uu____22624 =
                  let uu____22625 =
                    let uu____22630 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22630) in
                  FStar_Errors.Error uu____22625 in
                FStar_Exn.raise uu____22624))
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
      let fail uu____22682 =
        match uu____22682 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22696 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22696
       then
         let uu____22697 = wl_to_string wl in
         let uu____22698 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22697 uu____22698
       else ());
      (let g1 =
         let uu____22713 = solve_and_commit env wl fail in
         match uu____22713 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___216_22726 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___216_22726.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___216_22726.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___216_22726.FStar_TypeChecker_Env.implicits)
             }
         | uu____22731 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___217_22735 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___217_22735.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___217_22735.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___217_22735.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22758 = FStar_ST.op_Bang last_proof_ns in
    match uu____22758 with
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
            let uu___218_22945 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___218_22945.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___218_22945.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___218_22945.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22946 =
            let uu____22947 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22947 in
          if uu____22946
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22955 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22955
                   then
                     let uu____22956 = FStar_TypeChecker_Env.get_range env in
                     let uu____22957 =
                       let uu____22958 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22958 in
                     FStar_Errors.diag uu____22956 uu____22957
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22961 = check_trivial vc1 in
                   match uu____22961 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
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
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22971 in
                             FStar_Errors.diag uu____22969 uu____22970
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22976 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22976
                           then
                             let uu____22977 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22978 =
                               let uu____22979 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22979 in
                             FStar_Errors.diag uu____22977 uu____22978
                           else ());
                          (let vcs =
                             let uu____22990 = FStar_Options.use_tactics () in
                             if uu____22990
                             then
                               FStar_Options.with_saved_options
                                 (fun uu____23009  ->
                                    (let uu____23011 =
                                       FStar_Options.set_options
                                         FStar_Options.Set "--no_tactics" in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____23011);
                                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                      env vc2)
                             else
                               (let uu____23013 =
                                  let uu____23020 = FStar_Options.peek () in
                                  (env, vc2, uu____23020) in
                                [uu____23013]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____23054  ->
                                   match uu____23054 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____23065 = check_trivial goal1 in
                                       (match uu____23065 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____23067 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____23067
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____23074 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____23074
                                              then
                                                let uu____23075 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____23076 =
                                                  let uu____23077 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____23078 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____23077 uu____23078 in
                                                FStar_Errors.diag uu____23075
                                                  uu____23076
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
      let uu____23090 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23090 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23096 =
            let uu____23097 =
              let uu____23102 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____23102) in
            FStar_Errors.Error uu____23097 in
          FStar_Exn.raise uu____23096
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____23111 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____23111 with
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
          let uu____23133 = FStar_Syntax_Unionfind.find u in
          match uu____23133 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23136 -> false in
        let rec until_fixpoint acc implicits =
          let uu____23154 = acc in
          match uu____23154 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23240 = hd1 in
                   (match uu____23240 with
                    | (uu____23253,env,u,tm,k,r) ->
                        let uu____23259 = unresolved u in
                        if uu____23259
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____23290 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23290
                            then
                              let uu____23291 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23292 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23293 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23291 uu____23292 uu____23293
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___219_23296 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___219_23296.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___219_23296.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___219_23296.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___219_23296.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___219_23296.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___219_23296.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___219_23296.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___219_23296.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___219_23296.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___219_23296.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___219_23296.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___219_23296.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___219_23296.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___219_23296.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___219_23296.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___219_23296.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___219_23296.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___219_23296.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___219_23296.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___219_23296.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___219_23296.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___219_23296.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___219_23296.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___219_23296.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___219_23296.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___219_23296.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___219_23296.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___219_23296.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___219_23296.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___219_23296.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___219_23296.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___219_23296.FStar_TypeChecker_Env.dsenv)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____23299 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___220_23307 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___220_23307.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___220_23307.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___220_23307.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___220_23307.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___220_23307.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___220_23307.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___220_23307.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___220_23307.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___220_23307.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___220_23307.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___220_23307.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___220_23307.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___220_23307.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___220_23307.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___220_23307.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___220_23307.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___220_23307.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___220_23307.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___220_23307.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___220_23307.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___220_23307.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___220_23307.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___220_23307.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___220_23307.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___220_23307.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___220_23307.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___220_23307.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___220_23307.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___220_23307.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___220_23307.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___220_23307.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___220_23307.FStar_TypeChecker_Env.dsenv)
                                     }) tm1 in
                                match uu____23299 with
                                | (uu____23308,uu____23309,g1) -> g1
                              else
                                (let uu____23312 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___221_23320 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___221_23320.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___221_23320.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___221_23320.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___221_23320.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___221_23320.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___221_23320.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___221_23320.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___221_23320.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___221_23320.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___221_23320.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___221_23320.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___221_23320.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___221_23320.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___221_23320.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___221_23320.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___221_23320.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___221_23320.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___221_23320.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___221_23320.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___221_23320.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___221_23320.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___221_23320.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___221_23320.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___221_23320.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___221_23320.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___221_23320.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___221_23320.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___221_23320.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___221_23320.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___221_23320.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___221_23320.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___221_23320.FStar_TypeChecker_Env.dsenv)
                                      }) tm1 in
                                 match uu____23312 with
                                 | (uu____23321,uu____23322,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___222_23325 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___222_23325.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___222_23325.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___222_23325.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23328 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23334  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23328 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___223_23362 = g in
        let uu____23363 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___223_23362.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___223_23362.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___223_23362.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23363
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
        let uu____23421 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23421 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23434 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23434
      | (reason,uu____23436,uu____23437,e,t,r)::uu____23441 ->
          let uu____23468 =
            let uu____23469 =
              let uu____23474 =
                let uu____23475 = FStar_Syntax_Print.term_to_string t in
                let uu____23476 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23475 uu____23476 in
              (uu____23474, r) in
            FStar_Errors.Error uu____23469 in
          FStar_Exn.raise uu____23468
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___224_23485 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___224_23485.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___224_23485.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___224_23485.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23514 = try_teq false env t1 t2 in
        match uu____23514 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23518 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23518 with
             | FStar_Pervasives_Native.Some uu____23523 -> true
             | FStar_Pervasives_Native.None  -> false)