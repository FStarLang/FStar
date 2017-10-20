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
let abstract_guard_n:
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun bs  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
          let uu___165_96 = g in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___165_96.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___165_96.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___165_96.FStar_TypeChecker_Env.implicits)
          }
let abstract_guard:
  FStar_Syntax_Syntax.binder ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun b  -> fun g  -> abstract_guard_n [b] g
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
        let uu____133 = FStar_Util.set_is_empty s in
        if uu____133
        then ()
        else
          (let uu____135 =
             let uu____136 =
               let uu____137 =
                 let uu____138 =
                   let uu____141 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____141
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____138
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format2 "Guard has free variables (%s): %s" msg
                 uu____137 in
             FStar_Errors.Err uu____136 in
           FStar_Exn.raise uu____135)
let check_term:
  Prims.string ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun msg  ->
    fun env  ->
      fun t  ->
        let s = FStar_TypeChecker_Env.unbound_vars env t in
        let uu____165 = FStar_Util.set_is_empty s in
        if uu____165
        then ()
        else
          (let uu____167 =
             let uu____168 =
               let uu____169 = FStar_Syntax_Print.term_to_string t in
               let uu____170 =
                 let uu____171 =
                   let uu____174 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____174
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____171
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format3 "Term <%s> has free variables (%s): %s"
                 uu____169 msg uu____170 in
             FStar_Errors.Err uu____168 in
           FStar_Exn.raise uu____167)
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___166_192 = g in
          let uu____193 =
            let uu____194 =
              let uu____195 =
                let uu____198 =
                  let uu____199 =
                    let uu____214 =
                      let uu____217 = FStar_Syntax_Syntax.as_arg e in
                      [uu____217] in
                    (f, uu____214) in
                  FStar_Syntax_Syntax.Tm_app uu____199 in
                FStar_Syntax_Syntax.mk uu____198 in
              uu____195 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_41  -> FStar_TypeChecker_Common.NonTrivial _0_41)
              uu____194 in
          {
            FStar_TypeChecker_Env.guard_f = uu____193;
            FStar_TypeChecker_Env.deferred =
              (uu___166_192.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___166_192.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___166_192.FStar_TypeChecker_Env.implicits)
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
          let uu___167_237 = g in
          let uu____238 =
            let uu____239 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____239 in
          {
            FStar_TypeChecker_Env.guard_f = uu____238;
            FStar_TypeChecker_Env.deferred =
              (uu___167_237.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___167_237.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___167_237.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____244 -> failwith "impossible"
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
          let uu____257 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____257
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____262 =
      let uu____263 = FStar_Syntax_Util.unmeta t in
      uu____263.FStar_Syntax_Syntax.n in
    match uu____262 with
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
        let uu____303 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____303;
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
                       let uu____377 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____377
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___168_379 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___168_379.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___168_379.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___168_379.FStar_TypeChecker_Env.implicits)
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
               let uu____401 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____401
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
            let uu___169_417 = g in
            let uu____418 =
              let uu____419 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____419 in
            {
              FStar_TypeChecker_Env.guard_f = uu____418;
              FStar_TypeChecker_Env.deferred =
                (uu___169_417.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___169_417.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___169_417.FStar_TypeChecker_Env.implicits)
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
        | uu____452 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____477 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____477 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____485 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____485, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____516 = FStar_Syntax_Util.type_u () in
        match uu____516 with
        | (t_type,u) ->
            let uu____523 =
              let uu____528 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____528 t_type in
            (match uu____523 with
             | (tt,uu____530) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____564 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____606 -> false
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
    match projectee with | Success _0 -> true | uu____800 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____818 -> false
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
    match projectee with | COVARIANT  -> true | uu____843 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____848 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____853 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___137_877  ->
    match uu___137_877 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____884 =
        let uu____885 = FStar_Syntax_Subst.compress t in
        uu____885.FStar_Syntax_Syntax.n in
      match uu____884 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____914 = FStar_Syntax_Print.uvar_to_string u in
          let uu____915 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____914 uu____915
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____918;
             FStar_Syntax_Syntax.vars = uu____919;_},args)
          ->
          let uu____965 = FStar_Syntax_Print.uvar_to_string u in
          let uu____966 = FStar_Syntax_Print.term_to_string ty in
          let uu____967 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____965 uu____966 uu____967
      | uu____968 -> "--" in
    let uu____969 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____969 detail
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___138_977  ->
      match uu___138_977 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____983 =
            let uu____986 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____987 =
              let uu____990 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____991 =
                let uu____994 =
                  let uu____997 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____997] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____994 in
              uu____990 :: uu____991 in
            uu____986 :: uu____987 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____983
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1003 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____1004 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____1003
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1004
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___139_1012  ->
      match uu___139_1012 with
      | UNIV (u,t) ->
          let x =
            let uu____1016 = FStar_Options.hide_uvar_nums () in
            if uu____1016
            then "?"
            else
              (let uu____1018 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____1018 FStar_Util.string_of_int) in
          let uu____1019 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____1019
      | TERM ((u,uu____1021),t) ->
          let x =
            let uu____1028 = FStar_Options.hide_uvar_nums () in
            if uu____1028
            then "?"
            else
              (let uu____1030 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____1030 FStar_Util.string_of_int) in
          let uu____1031 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____1031
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____1044 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____1044 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____1057 =
      let uu____1060 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1060
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1057 (FStar_String.concat ", ")
let args_to_string:
  'Auu____1073 .
    (FStar_Syntax_Syntax.term,'Auu____1073) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1090 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1108  ->
              match uu____1108 with
              | (x,uu____1114) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1090 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1121 =
      let uu____1122 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1122 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1121;
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
        let uu___170_1141 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___170_1141.wl_deferred);
          ctr = (uu___170_1141.ctr);
          defer_ok = (uu___170_1141.defer_ok);
          smt_ok;
          tcenv = (uu___170_1141.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1156 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1156,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___171_1177 = empty_worklist env in
      let uu____1178 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1178;
        wl_deferred = (uu___171_1177.wl_deferred);
        ctr = (uu___171_1177.ctr);
        defer_ok = false;
        smt_ok = (uu___171_1177.smt_ok);
        tcenv = (uu___171_1177.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___172_1195 = wl in
        {
          attempting = (uu___172_1195.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___172_1195.ctr);
          defer_ok = (uu___172_1195.defer_ok);
          smt_ok = (uu___172_1195.smt_ok);
          tcenv = (uu___172_1195.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___173_1214 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___173_1214.wl_deferred);
        ctr = (uu___173_1214.ctr);
        defer_ok = (uu___173_1214.defer_ok);
        smt_ok = (uu___173_1214.smt_ok);
        tcenv = (uu___173_1214.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1228 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1228
         then
           let uu____1229 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1229
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___140_1234  ->
    match uu___140_1234 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1241 'Auu____1242 .
    ('Auu____1242,'Auu____1241) FStar_TypeChecker_Common.problem ->
      ('Auu____1242,'Auu____1241) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___174_1259 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___174_1259.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___174_1259.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___174_1259.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___174_1259.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___174_1259.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___174_1259.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___174_1259.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1270 'Auu____1271 .
    ('Auu____1271,'Auu____1270) FStar_TypeChecker_Common.problem ->
      ('Auu____1271,'Auu____1270) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___141_1292  ->
    match uu___141_1292 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___142_1318  ->
      match uu___142_1318 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___143_1322  ->
    match uu___143_1322 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___144_1336  ->
    match uu___144_1336 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___145_1352  ->
    match uu___145_1352 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___146_1368  ->
    match uu___146_1368 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___147_1386  ->
    match uu___147_1386 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___148_1404  ->
    match uu___148_1404 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___149_1418  ->
    match uu___149_1418 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.TProb _0_44) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.CProb _0_45) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1441 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1441 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1454  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1555 'Auu____1556 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1556 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1556 ->
              'Auu____1555 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1556,'Auu____1555)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1593 = next_pid () in
                let uu____1594 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1593;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1594;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1617 'Auu____1618 .
    FStar_TypeChecker_Env.env ->
      'Auu____1618 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1618 ->
            'Auu____1617 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1618,'Auu____1617)
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
                let uu____1656 = next_pid () in
                let uu____1657 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1656;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1657;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1678 'Auu____1679 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1679 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1679 ->
            'Auu____1678 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1679,'Auu____1678) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1712 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1712;
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
  'Auu____1723 .
    worklist ->
      ('Auu____1723,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1776 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1776
        then
          let uu____1777 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1778 = prob_to_string env d in
          let uu____1779 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1777 uu____1778 uu____1779 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1785 -> failwith "impossible" in
           let uu____1786 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1800 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1801 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1800, uu____1801)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1807 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1808 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1807, uu____1808) in
           match uu____1786 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___150_1825  ->
            match uu___150_1825 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1837 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1839),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___151_1861  ->
           match uu___151_1861 with
           | UNIV uu____1864 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1870),t) ->
               let uu____1876 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1876
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
        (fun uu___152_1898  ->
           match uu___152_1898 with
           | UNIV (u',t) ->
               let uu____1903 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1903
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1907 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1916 =
        let uu____1917 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1917 in
      FStar_Syntax_Subst.compress uu____1916
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1926 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1926
let norm_arg:
  'Auu____1933 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1933) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1933)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1954 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1954, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1987  ->
              match uu____1987 with
              | (x,imp) ->
                  let uu____1998 =
                    let uu___175_1999 = x in
                    let uu____2000 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___175_1999.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___175_1999.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2000
                    } in
                  (uu____1998, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2017 = aux u3 in FStar_Syntax_Syntax.U_succ uu____2017
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2021 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____2021
        | uu____2024 -> u2 in
      let uu____2025 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2025
let normalize_refinement:
  'Auu____2036 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2036 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement:
  'Auu____2061 .
    FStar_TypeChecker_Env.env ->
      'Auu____2061 ->
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
                (let uu____2163 =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 match uu____2163 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2180;
                     FStar_Syntax_Syntax.vars = uu____2181;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2207 =
                       let uu____2208 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2209 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2208 uu____2209 in
                     failwith uu____2207)
          | FStar_Syntax_Syntax.Tm_uinst uu____2224 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 let uu____2261 =
                   let uu____2262 = FStar_Syntax_Subst.compress t1' in
                   uu____2262.FStar_Syntax_Syntax.n in
                 match uu____2261 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2279 -> aux true t1'
                 | uu____2286 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2301 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 let uu____2332 =
                   let uu____2333 = FStar_Syntax_Subst.compress t1' in
                   uu____2333.FStar_Syntax_Syntax.n in
                 match uu____2332 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2350 -> aux true t1'
                 | uu____2357 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2372 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement
                     [FStar_TypeChecker_Normalize.Weak;
                     FStar_TypeChecker_Normalize.HNF] env wl t12 in
                 let uu____2417 =
                   let uu____2418 = FStar_Syntax_Subst.compress t1' in
                   uu____2418.FStar_Syntax_Syntax.n in
                 match uu____2417 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2435 -> aux true t1'
                 | uu____2442 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2457 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2472 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2487 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2502 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2517 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2544 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2575 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2606 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2633 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2670 ->
              let uu____2677 =
                let uu____2678 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2679 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2678 uu____2679 in
              failwith uu____2677
          | FStar_Syntax_Syntax.Tm_ascribed uu____2694 ->
              let uu____2721 =
                let uu____2722 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2723 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2722 uu____2723 in
              failwith uu____2721
          | FStar_Syntax_Syntax.Tm_delayed uu____2738 ->
              let uu____2763 =
                let uu____2764 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2765 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2764 uu____2765 in
              failwith uu____2763
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2780 =
                let uu____2781 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2782 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2781 uu____2782 in
              failwith uu____2780 in
        let uu____2797 = whnf env t1 in aux false uu____2797
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2806 =
        let uu____2821 = empty_worklist env in
        base_and_refinement env uu____2821 t in
      FStar_All.pipe_right uu____2806 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2856 = FStar_Syntax_Syntax.null_bv t in
    (uu____2856, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2865 .
    FStar_TypeChecker_Env.env ->
      'Auu____2865 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2882 = base_and_refinement env wl t in
        match uu____2882 with
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
  fun uu____2962  ->
    match uu____2962 with
    | (t_base,refopt) ->
        let uu____2989 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2989 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____3024 =
      let uu____3027 =
        let uu____3030 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3053  ->
                  match uu____3053 with | (uu____3060,uu____3061,x) -> x)) in
        FStar_List.append wl.attempting uu____3030 in
      FStar_List.map (wl_prob_to_string wl) uu____3027 in
    FStar_All.pipe_right uu____3024 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3077 =
          let uu____3090 =
            let uu____3091 = FStar_Syntax_Subst.compress k in
            uu____3091.FStar_Syntax_Syntax.n in
          match uu____3090 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3144 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3144)
              else
                (let uu____3158 = FStar_Syntax_Util.abs_formals t in
                 match uu____3158 with
                 | (ys',t1,uu____3181) ->
                     let uu____3186 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3186))
          | uu____3227 ->
              let uu____3228 =
                let uu____3239 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3239) in
              ((ys, t), uu____3228) in
        match uu____3077 with
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
                 let uu____3288 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3288 c in
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
            let uu____3321 = p_guard prob in
            match uu____3321 with
            | (uu____3326,uv) ->
                ((let uu____3329 =
                    let uu____3330 = FStar_Syntax_Subst.compress uv in
                    uu____3330.FStar_Syntax_Syntax.n in
                  match uu____3329 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3362 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3362
                        then
                          let uu____3363 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3364 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3365 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3363
                            uu____3364 uu____3365
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3367 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___176_3370 = wl in
                  {
                    attempting = (uu___176_3370.attempting);
                    wl_deferred = (uu___176_3370.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___176_3370.defer_ok);
                    smt_ok = (uu___176_3370.smt_ok);
                    tcenv = (uu___176_3370.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3388 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3388
         then
           let uu____3389 = FStar_Util.string_of_int pid in
           let uu____3390 =
             let uu____3391 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3391 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3389 uu____3390
         else ());
        commit sol;
        (let uu___177_3398 = wl in
         {
           attempting = (uu___177_3398.attempting);
           wl_deferred = (uu___177_3398.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___177_3398.defer_ok);
           smt_ok = (uu___177_3398.smt_ok);
           tcenv = (uu___177_3398.tcenv)
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
            | (uu____3440,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3452 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3452 in
          (let uu____3458 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3458
           then
             let uu____3459 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3460 =
               let uu____3461 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3461 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3459 uu____3460
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
        let uu____3496 =
          let uu____3503 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3503 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3496
          (FStar_Util.for_some
             (fun uu____3539  ->
                match uu____3539 with
                | (uv,uu____3545) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3558 'Auu____3559 .
    'Auu____3559 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3558)
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
            let uu____3591 = occurs wl uk t in Prims.op_Negation uu____3591 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3598 =
                 let uu____3599 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3600 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3599 uu____3600 in
               FStar_Pervasives_Native.Some uu____3598) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3617 'Auu____3618 .
    'Auu____3618 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3617)
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
            let uu____3672 = occurs_check env wl uk t in
            match uu____3672 with
            | (occurs_ok,msg) ->
                let uu____3703 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3703, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3730 'Auu____3731 .
    (FStar_Syntax_Syntax.bv,'Auu____3731) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3730) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3730) FStar_Pervasives_Native.tuple2
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
      let uu____3815 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3869  ->
                fun uu____3870  ->
                  match (uu____3869, uu____3870) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3951 =
                        let uu____3952 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3952 in
                      if uu____3951
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3977 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3977
                         then
                           let uu____3990 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3990)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3815 with | (isect,uu____4031) -> FStar_List.rev isect
let binders_eq:
  'Auu____4060 'Auu____4061 .
    (FStar_Syntax_Syntax.bv,'Auu____4061) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4060) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4116  ->
              fun uu____4117  ->
                match (uu____4116, uu____4117) with
                | ((a,uu____4135),(b,uu____4137)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4156 'Auu____4157 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4157) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4156)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4156)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4208 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4222  ->
                      match uu____4222 with
                      | (b,uu____4228) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4208
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4244 -> FStar_Pervasives_Native.None
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
            let uu____4319 = pat_var_opt env seen hd1 in
            (match uu____4319 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4333 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4333
                   then
                     let uu____4334 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4334
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4353 =
      let uu____4354 = FStar_Syntax_Subst.compress t in
      uu____4354.FStar_Syntax_Syntax.n in
    match uu____4353 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4357 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4374;
           FStar_Syntax_Syntax.pos = uu____4375;
           FStar_Syntax_Syntax.vars = uu____4376;_},uu____4377)
        -> true
    | uu____4414 -> false
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
           FStar_Syntax_Syntax.pos = uu____4539;
           FStar_Syntax_Syntax.vars = uu____4540;_},args)
        -> (t, uv, k, args)
    | uu____4608 -> failwith "Not a flex-uvar"
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
      let uu____4687 = destruct_flex_t t in
      match uu____4687 with
      | (t1,uv,k,args) ->
          let uu____4802 = pat_vars env [] args in
          (match uu____4802 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4900 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4982 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5019 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5024 -> false
let head_match: match_result -> match_result =
  fun uu___153_5028  ->
    match uu___153_5028 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5043 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5054 ->
          let uu____5055 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5055 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5066 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5087 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5096 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5123 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5124 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5125 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5142 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5155 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5179) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5185,uu____5186) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5228) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5249;
             FStar_Syntax_Syntax.index = uu____5250;
             FStar_Syntax_Syntax.sort = t2;_},uu____5252)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5259 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5260 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5261 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5274 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5292 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5292
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
            let uu____5316 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5316
            then FullMatch
            else
              (let uu____5318 =
                 let uu____5327 =
                   let uu____5330 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5330 in
                 let uu____5331 =
                   let uu____5334 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5334 in
                 (uu____5327, uu____5331) in
               MisMatch uu____5318)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5340),FStar_Syntax_Syntax.Tm_uinst (g,uu____5342)) ->
            let uu____5351 = head_matches env f g in
            FStar_All.pipe_right uu____5351 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5360),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5362)) ->
            let uu____5411 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5411
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5418),FStar_Syntax_Syntax.Tm_refine (y,uu____5420)) ->
            let uu____5429 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5429 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5431),uu____5432) ->
            let uu____5437 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5437 head_match
        | (uu____5438,FStar_Syntax_Syntax.Tm_refine (x,uu____5440)) ->
            let uu____5445 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5445 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5446,FStar_Syntax_Syntax.Tm_type
           uu____5447) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5448,FStar_Syntax_Syntax.Tm_arrow uu____5449) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5475),FStar_Syntax_Syntax.Tm_app (head',uu____5477))
            ->
            let uu____5518 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5518 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5520),uu____5521) ->
            let uu____5542 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5542 head_match
        | (uu____5543,FStar_Syntax_Syntax.Tm_app (head1,uu____5545)) ->
            let uu____5566 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5566 head_match
        | uu____5567 ->
            let uu____5572 =
              let uu____5581 = delta_depth_of_term env t11 in
              let uu____5584 = delta_depth_of_term env t21 in
              (uu____5581, uu____5584) in
            MisMatch uu____5572
let head_matches_delta:
  'Auu____5601 .
    FStar_TypeChecker_Env.env ->
      'Auu____5601 ->
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
            let uu____5634 = FStar_Syntax_Util.head_and_args t in
            match uu____5634 with
            | (head1,uu____5652) ->
                let uu____5673 =
                  let uu____5674 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5674.FStar_Syntax_Syntax.n in
                (match uu____5673 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5680 =
                       let uu____5681 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5681 FStar_Option.isSome in
                     if uu____5680
                     then
                       let uu____5700 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5700
                         (fun _0_46  -> FStar_Pervasives_Native.Some _0_46)
                     else FStar_Pervasives_Native.None
                 | uu____5704 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5807)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5825 =
                     let uu____5834 = maybe_inline t11 in
                     let uu____5837 = maybe_inline t21 in
                     (uu____5834, uu____5837) in
                   match uu____5825 with
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
                (uu____5874,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5892 =
                     let uu____5901 = maybe_inline t11 in
                     let uu____5904 = maybe_inline t21 in
                     (uu____5901, uu____5904) in
                   match uu____5892 with
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
                let uu____5947 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5947 with
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
                let uu____5970 =
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
                (match uu____5970 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5994 -> fail r
            | uu____6003 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6037 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6075 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___154_6089  ->
    match uu___154_6089 with
    | T (t,uu____6091) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6109 = FStar_Syntax_Util.type_u () in
      match uu____6109 with
      | (t,uu____6115) ->
          let uu____6116 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6116
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6129 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6129 FStar_Pervasives_Native.fst
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
        let uu____6195 = head_matches env t1 t' in
        match uu____6195 with
        | MisMatch uu____6196 -> false
        | uu____6205 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6301,imp),T (t2,uu____6304)) -> (t2, imp)
                     | uu____6323 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6390  ->
                    match uu____6390 with
                    | (t2,uu____6404) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6447 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6447 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6522))::tcs2) ->
                       aux
                         (((let uu___178_6557 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_6557.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_6557.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6575 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___155_6628 =
                 match uu___155_6628 with
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
               let uu____6745 = decompose1 [] bs1 in
               (rebuild, matches, uu____6745))
      | uu____6794 ->
          let rebuild uu___156_6800 =
            match uu___156_6800 with
            | [] -> t1
            | uu____6803 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___157_6835  ->
    match uu___157_6835 with
    | T (t,uu____6837) -> t
    | uu____6846 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___158_6850  ->
    match uu___158_6850 with
    | T (t,uu____6852) -> FStar_Syntax_Syntax.as_arg t
    | uu____6861 -> failwith "Impossible"
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
              | (uu____6972,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6997 = new_uvar r scope1 k in
                  (match uu____6997 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7015 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7032 =
                         let uu____7033 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_47  ->
                              FStar_TypeChecker_Common.TProb _0_47)
                           uu____7033 in
                       ((T (gi_xs, mk_kind)), uu____7032))
              | (uu____7046,uu____7047,C uu____7048) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7195 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7212;
                         FStar_Syntax_Syntax.vars = uu____7213;_})
                        ->
                        let uu____7236 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7236 with
                         | (T (gi_xs,uu____7260),prob) ->
                             let uu____7270 =
                               let uu____7271 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7271 in
                             (uu____7270, [prob])
                         | uu____7274 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7289;
                         FStar_Syntax_Syntax.vars = uu____7290;_})
                        ->
                        let uu____7313 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7313 with
                         | (T (gi_xs,uu____7337),prob) ->
                             let uu____7347 =
                               let uu____7348 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_49  -> C _0_49)
                                 uu____7348 in
                             (uu____7347, [prob])
                         | uu____7351 -> failwith "impossible")
                    | (uu____7362,uu____7363,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7365;
                         FStar_Syntax_Syntax.vars = uu____7366;_})
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
                        let uu____7497 =
                          let uu____7506 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7506 FStar_List.unzip in
                        (match uu____7497 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7560 =
                                 let uu____7561 =
                                   let uu____7564 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7564 un_T in
                                 let uu____7565 =
                                   let uu____7574 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7574
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7561;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7565;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7560 in
                             ((C gi_xs), sub_probs))
                    | uu____7583 ->
                        let uu____7596 = sub_prob scope1 args q in
                        (match uu____7596 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7195 with
                   | (tc,probs) ->
                       let uu____7627 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7690,uu____7691),T
                            (t,uu____7693)) ->
                             let b1 =
                               ((let uu___179_7730 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___179_7730.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___179_7730.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7731 =
                               let uu____7738 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7738 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7731)
                         | uu____7773 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7627 with
                        | (bopt,scope2,args1) ->
                            let uu____7857 = aux scope2 args1 qs2 in
                            (match uu____7857 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7894 =
                                         let uu____7897 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7897 in
                                       FStar_Syntax_Util.mk_conj_l uu____7894
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7920 =
                                         let uu____7923 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7924 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7923 :: uu____7924 in
                                       FStar_Syntax_Util.mk_conj_l uu____7920 in
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
  'Auu____7995 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7995)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7995)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___180_8016 = p in
      let uu____8021 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8022 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___180_8016.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8021;
        FStar_TypeChecker_Common.relation =
          (uu___180_8016.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8022;
        FStar_TypeChecker_Common.element =
          (uu___180_8016.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___180_8016.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___180_8016.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___180_8016.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___180_8016.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___180_8016.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8036 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8036
            (fun _0_50  -> FStar_TypeChecker_Common.TProb _0_50)
      | FStar_TypeChecker_Common.CProb uu____8045 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8067 = compress_prob wl pr in
        FStar_All.pipe_right uu____8067 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8077 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8077 with
           | (lh,uu____8097) ->
               let uu____8118 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8118 with
                | (rh,uu____8138) ->
                    let uu____8159 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8176,FStar_Syntax_Syntax.Tm_uvar uu____8177)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8214,uu____8215)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8236,FStar_Syntax_Syntax.Tm_uvar uu____8237)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8258,uu____8259)
                          ->
                          let uu____8276 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8276 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8339 ->
                                    let rank =
                                      let uu____8349 = is_top_level_prob prob in
                                      if uu____8349
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8351 =
                                      let uu___181_8356 = tp in
                                      let uu____8361 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___181_8356.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___181_8356.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___181_8356.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8361;
                                        FStar_TypeChecker_Common.element =
                                          (uu___181_8356.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___181_8356.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___181_8356.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___181_8356.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___181_8356.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___181_8356.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8351)))
                      | (uu____8376,FStar_Syntax_Syntax.Tm_uvar uu____8377)
                          ->
                          let uu____8394 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8394 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8457 ->
                                    let uu____8466 =
                                      let uu___182_8473 = tp in
                                      let uu____8478 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___182_8473.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8478;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___182_8473.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___182_8473.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___182_8473.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___182_8473.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___182_8473.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___182_8473.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___182_8473.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___182_8473.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8466)))
                      | (uu____8499,uu____8500) -> (rigid_rigid, tp) in
                    (match uu____8159 with
                     | (rank,tp1) ->
                         let uu____8519 =
                           FStar_All.pipe_right
                             (let uu___183_8525 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___183_8525.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___183_8525.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___183_8525.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___183_8525.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___183_8525.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___183_8525.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___183_8525.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___183_8525.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___183_8525.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_51  ->
                                FStar_TypeChecker_Common.TProb _0_51) in
                         (rank, uu____8519))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8535 =
            FStar_All.pipe_right
              (let uu___184_8541 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___184_8541.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___184_8541.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___184_8541.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___184_8541.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___184_8541.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___184_8541.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___184_8541.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___184_8541.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___184_8541.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_52  -> FStar_TypeChecker_Common.CProb _0_52) in
          (rigid_rigid, uu____8535)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8597 probs =
      match uu____8597 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8650 = rank wl hd1 in
               (match uu____8650 with
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
    match projectee with | UDeferred _0 -> true | uu____8760 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8774 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8788 -> false
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
                        let uu____8833 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8833 with
                        | (k,uu____8839) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8849 -> false)))
            | uu____8850 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8901 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8901 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8904 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8914 =
                     let uu____8915 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8916 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8915
                       uu____8916 in
                   UFailed uu____8914)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8936 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8936 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8958 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8958 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8961 ->
                let uu____8966 =
                  let uu____8967 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8968 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8967
                    uu____8968 msg in
                UFailed uu____8966 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8969,uu____8970) ->
              let uu____8971 =
                let uu____8972 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8973 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8972 uu____8973 in
              failwith uu____8971
          | (FStar_Syntax_Syntax.U_unknown ,uu____8974) ->
              let uu____8975 =
                let uu____8976 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8977 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8976 uu____8977 in
              failwith uu____8975
          | (uu____8978,FStar_Syntax_Syntax.U_bvar uu____8979) ->
              let uu____8980 =
                let uu____8981 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8982 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8981 uu____8982 in
              failwith uu____8980
          | (uu____8983,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8984 =
                let uu____8985 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8986 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8985 uu____8986 in
              failwith uu____8984
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9010 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9010
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9032 = occurs_univ v1 u3 in
              if uu____9032
              then
                let uu____9033 =
                  let uu____9034 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9035 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9034 uu____9035 in
                try_umax_components u11 u21 uu____9033
              else
                (let uu____9037 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9037)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9057 = occurs_univ v1 u3 in
              if uu____9057
              then
                let uu____9058 =
                  let uu____9059 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9060 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9059 uu____9060 in
                try_umax_components u11 u21 uu____9058
              else
                (let uu____9062 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9062)
          | (FStar_Syntax_Syntax.U_max uu____9071,uu____9072) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9078 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9078
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9080,FStar_Syntax_Syntax.U_max uu____9081) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9087 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9087
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9089,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9090,FStar_Syntax_Syntax.U_name
             uu____9091) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9092) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9093) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9094,FStar_Syntax_Syntax.U_succ
             uu____9095) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9096,FStar_Syntax_Syntax.U_zero
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
      let uu____9190 = bc1 in
      match uu____9190 with
      | (bs1,mk_cod1) ->
          let uu____9231 = bc2 in
          (match uu____9231 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9301 = FStar_Util.first_N n1 bs in
                 match uu____9301 with
                 | (bs3,rest) ->
                     let uu____9326 = mk_cod rest in (bs3, uu____9326) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9355 =
                   let uu____9362 = mk_cod1 [] in (bs1, uu____9362) in
                 let uu____9365 =
                   let uu____9372 = mk_cod2 [] in (bs2, uu____9372) in
                 (uu____9355, uu____9365)
               else
                 if l1 > l2
                 then
                   (let uu____9414 = curry l2 bs1 mk_cod1 in
                    let uu____9427 =
                      let uu____9434 = mk_cod2 [] in (bs2, uu____9434) in
                    (uu____9414, uu____9427))
                 else
                   (let uu____9450 =
                      let uu____9457 = mk_cod1 [] in (bs1, uu____9457) in
                    let uu____9460 = curry l1 bs2 mk_cod2 in
                    (uu____9450, uu____9460)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9581 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9581
       then
         let uu____9582 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9582
       else ());
      (let uu____9584 = next_prob probs in
       match uu____9584 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___185_9605 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___185_9605.wl_deferred);
               ctr = (uu___185_9605.ctr);
               defer_ok = (uu___185_9605.defer_ok);
               smt_ok = (uu___185_9605.smt_ok);
               tcenv = (uu___185_9605.tcenv)
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
                  let uu____9616 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9616 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9621 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9621 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9626,uu____9627) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9644 ->
                let uu____9653 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9712  ->
                          match uu____9712 with
                          | (c,uu____9720,uu____9721) -> c < probs.ctr)) in
                (match uu____9653 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9762 =
                            FStar_List.map
                              (fun uu____9777  ->
                                 match uu____9777 with
                                 | (uu____9788,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9762
                      | uu____9791 ->
                          let uu____9800 =
                            let uu___186_9801 = probs in
                            let uu____9802 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9823  ->
                                      match uu____9823 with
                                      | (uu____9830,uu____9831,y) -> y)) in
                            {
                              attempting = uu____9802;
                              wl_deferred = rest;
                              ctr = (uu___186_9801.ctr);
                              defer_ok = (uu___186_9801.defer_ok);
                              smt_ok = (uu___186_9801.smt_ok);
                              tcenv = (uu___186_9801.tcenv)
                            } in
                          solve env uu____9800))))
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
            let uu____9838 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9838 with
            | USolved wl1 ->
                let uu____9840 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9840
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
                  let uu____9886 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9886 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9889 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9901;
                  FStar_Syntax_Syntax.vars = uu____9902;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9905;
                  FStar_Syntax_Syntax.vars = uu____9906;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9920,uu____9921) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9928,FStar_Syntax_Syntax.Tm_uinst uu____9929) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9936 -> USolved wl
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
            ((let uu____9946 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9946
              then
                let uu____9947 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9947 msg
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
        (let uu____9956 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9956
         then
           let uu____9957 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9957
         else ());
        (let uu____9959 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9959 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10021 = head_matches_delta env () t1 t2 in
               match uu____10021 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10062 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10111 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10126 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10127 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10126, uu____10127)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10132 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10133 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10132, uu____10133) in
                        (match uu____10111 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10159 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_53  ->
                                    FStar_TypeChecker_Common.TProb _0_53)
                                 uu____10159 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10190 =
                                    let uu____10199 =
                                      let uu____10202 =
                                        let uu____10205 =
                                          let uu____10206 =
                                            let uu____10213 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10213) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10206 in
                                        FStar_Syntax_Syntax.mk uu____10205 in
                                      uu____10202
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10221 =
                                      let uu____10224 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10224] in
                                    (uu____10199, uu____10221) in
                                  FStar_Pervasives_Native.Some uu____10190
                              | (uu____10237,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10239)) ->
                                  let uu____10244 =
                                    let uu____10251 =
                                      let uu____10254 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10254] in
                                    (t11, uu____10251) in
                                  FStar_Pervasives_Native.Some uu____10244
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10264),uu____10265) ->
                                  let uu____10270 =
                                    let uu____10277 =
                                      let uu____10280 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10280] in
                                    (t21, uu____10277) in
                                  FStar_Pervasives_Native.Some uu____10270
                              | uu____10289 ->
                                  let uu____10294 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10294 with
                                   | (head1,uu____10318) ->
                                       let uu____10339 =
                                         let uu____10340 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10340.FStar_Syntax_Syntax.n in
                                       (match uu____10339 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10351;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10353;_}
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
                                        | uu____10360 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10373) ->
                  let uu____10398 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___159_10424  ->
                            match uu___159_10424 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10431 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10431 with
                                      | (u',uu____10447) ->
                                          let uu____10468 =
                                            let uu____10469 = whnf env u' in
                                            uu____10469.FStar_Syntax_Syntax.n in
                                          (match uu____10468 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10473) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10498 -> false))
                                 | uu____10499 -> false)
                            | uu____10502 -> false)) in
                  (match uu____10398 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10536 tps =
                         match uu____10536 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10584 =
                                    let uu____10593 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10593 in
                                  (match uu____10584 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10628 -> FStar_Pervasives_Native.None) in
                       let uu____10637 =
                         let uu____10646 =
                           let uu____10653 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10653, []) in
                         make_lower_bound uu____10646 lower_bounds in
                       (match uu____10637 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10665 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10665
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
                            ((let uu____10685 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10685
                              then
                                let wl' =
                                  let uu___187_10687 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___187_10687.wl_deferred);
                                    ctr = (uu___187_10687.ctr);
                                    defer_ok = (uu___187_10687.defer_ok);
                                    smt_ok = (uu___187_10687.smt_ok);
                                    tcenv = (uu___187_10687.tcenv)
                                  } in
                                let uu____10688 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10688
                              else ());
                             (let uu____10690 =
                                solve_t env eq_prob
                                  (let uu___188_10692 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___188_10692.wl_deferred);
                                     ctr = (uu___188_10692.ctr);
                                     defer_ok = (uu___188_10692.defer_ok);
                                     smt_ok = (uu___188_10692.smt_ok);
                                     tcenv = (uu___188_10692.tcenv)
                                   }) in
                              match uu____10690 with
                              | Success uu____10695 ->
                                  let wl1 =
                                    let uu___189_10697 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___189_10697.wl_deferred);
                                      ctr = (uu___189_10697.ctr);
                                      defer_ok = (uu___189_10697.defer_ok);
                                      smt_ok = (uu___189_10697.smt_ok);
                                      tcenv = (uu___189_10697.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10699 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10704 -> FStar_Pervasives_Native.None))))
              | uu____10705 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10714 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10714
         then
           let uu____10715 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10715
         else ());
        (let uu____10717 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10717 with
         | (u,args) ->
             let uu____10756 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10756 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10797 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10797 with
                    | (h1,args1) ->
                        let uu____10838 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10838 with
                         | (h2,uu____10858) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10885 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10885
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10903 =
                                          let uu____10906 =
                                            let uu____10907 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10907 in
                                          [uu____10906] in
                                        FStar_Pervasives_Native.Some
                                          uu____10903))
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
                                       (let uu____10940 =
                                          let uu____10943 =
                                            let uu____10944 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_55  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_55) uu____10944 in
                                          [uu____10943] in
                                        FStar_Pervasives_Native.Some
                                          uu____10940))
                                  else FStar_Pervasives_Native.None
                              | uu____10958 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11048 =
                               let uu____11057 =
                                 let uu____11060 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11060 in
                               (uu____11057, m1) in
                             FStar_Pervasives_Native.Some uu____11048)
                    | (uu____11073,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11075)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11123),uu____11124) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11171 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11224) ->
                       let uu____11249 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___160_11275  ->
                                 match uu___160_11275 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11282 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11282 with
                                           | (u',uu____11298) ->
                                               let uu____11319 =
                                                 let uu____11320 =
                                                   whnf env u' in
                                                 uu____11320.FStar_Syntax_Syntax.n in
                                               (match uu____11319 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11324) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11349 -> false))
                                      | uu____11350 -> false)
                                 | uu____11353 -> false)) in
                       (match uu____11249 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11391 tps =
                              match uu____11391 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11453 =
                                         let uu____11464 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11464 in
                                       (match uu____11453 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11515 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11526 =
                              let uu____11537 =
                                let uu____11546 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11546, []) in
                              make_upper_bound uu____11537 upper_bounds in
                            (match uu____11526 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11560 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11560
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
                                 ((let uu____11586 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11586
                                   then
                                     let wl' =
                                       let uu___190_11588 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___190_11588.wl_deferred);
                                         ctr = (uu___190_11588.ctr);
                                         defer_ok = (uu___190_11588.defer_ok);
                                         smt_ok = (uu___190_11588.smt_ok);
                                         tcenv = (uu___190_11588.tcenv)
                                       } in
                                     let uu____11589 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11589
                                   else ());
                                  (let uu____11591 =
                                     solve_t env eq_prob
                                       (let uu___191_11593 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___191_11593.wl_deferred);
                                          ctr = (uu___191_11593.ctr);
                                          defer_ok =
                                            (uu___191_11593.defer_ok);
                                          smt_ok = (uu___191_11593.smt_ok);
                                          tcenv = (uu___191_11593.tcenv)
                                        }) in
                                   match uu____11591 with
                                   | Success uu____11596 ->
                                       let wl1 =
                                         let uu___192_11598 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___192_11598.wl_deferred);
                                           ctr = (uu___192_11598.ctr);
                                           defer_ok =
                                             (uu___192_11598.defer_ok);
                                           smt_ok = (uu___192_11598.smt_ok);
                                           tcenv = (uu___192_11598.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11600 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11605 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11606 -> failwith "Impossible: Not a flex-rigid")))
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
                    let rhs_prob = rhs scope env1 subst1 in
                    ((let uu____11681 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11681
                      then
                        let uu____11682 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11682
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___193_11736 = hd1 in
                      let uu____11737 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___193_11736.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___193_11736.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11737
                      } in
                    let hd21 =
                      let uu___194_11741 = hd2 in
                      let uu____11742 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___194_11741.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___194_11741.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11742
                      } in
                    let prob =
                      let uu____11746 =
                        let uu____11751 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11751 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_56  -> FStar_TypeChecker_Common.TProb _0_56)
                        uu____11746 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11762 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11762 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11766 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11766 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11804 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11809 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11804 uu____11809 in
                         ((let uu____11819 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11819
                           then
                             let uu____11820 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11821 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11820 uu____11821
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11844 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11854 = aux scope env [] bs1 bs2 in
              match uu____11854 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11878 = compress_tprob wl problem in
        solve_t' env uu____11878 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11911 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11911 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11942,uu____11943) ->
                   let rec may_relate head3 =
                     let uu____11968 =
                       let uu____11969 = FStar_Syntax_Subst.compress head3 in
                       uu____11969.FStar_Syntax_Syntax.n in
                     match uu____11968 with
                     | FStar_Syntax_Syntax.Tm_name uu____11972 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11973 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11996;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11997;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12000;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12001;
                           FStar_Syntax_Syntax.fv_qual = uu____12002;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12006,uu____12007) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12049) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12055) ->
                         may_relate t
                     | uu____12060 -> false in
                   let uu____12061 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12061
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
                                let uu____12078 =
                                  let uu____12079 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12079 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12078 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12081 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12081
                   else
                     (let uu____12083 =
                        let uu____12084 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12085 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12084 uu____12085 in
                      giveup env1 uu____12083 orig)
               | (uu____12086,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___195_12100 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___195_12100.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___195_12100.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___195_12100.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___195_12100.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___195_12100.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___195_12100.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___195_12100.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___195_12100.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12101,FStar_Pervasives_Native.None ) ->
                   ((let uu____12113 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12113
                     then
                       let uu____12114 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12115 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12116 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12117 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12114
                         uu____12115 uu____12116 uu____12117
                     else ());
                    (let uu____12119 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12119 with
                     | (head11,args1) ->
                         let uu____12156 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12156 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12210 =
                                  let uu____12211 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12212 = args_to_string args1 in
                                  let uu____12213 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12214 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12211 uu____12212 uu____12213
                                    uu____12214 in
                                giveup env1 uu____12210 orig
                              else
                                (let uu____12216 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12222 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12222 = FStar_Syntax_Util.Equal) in
                                 if uu____12216
                                 then
                                   let uu____12223 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12223 with
                                   | USolved wl2 ->
                                       let uu____12225 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12225
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12229 =
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12229 with
                                    | (base1,refinement1) ->
                                        let uu____12266 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12266 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12347 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12347 with
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
                                                           (fun uu____12369 
                                                              ->
                                                              fun uu____12370
                                                                 ->
                                                                match 
                                                                  (uu____12369,
                                                                    uu____12370)
                                                                with
                                                                | ((a,uu____12388),
                                                                   (a',uu____12390))
                                                                    ->
                                                                    let uu____12399
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
                                                                    _0_57  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_57)
                                                                    uu____12399)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12409 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12409 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12415 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___196_12463 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___196_12463.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12502 =
          match uu____12502 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12718  ->
                              match uu____12718 with
                              | (x,imp) ->
                                  let uu____12729 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12729, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12742 = FStar_Syntax_Util.type_u () in
                      match uu____12742 with
                      | (t1,uu____12748) ->
                          let uu____12749 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12749 in
                    let uu____12754 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12754 with
                     | (t',tm_u1) ->
                         let uu____12767 = destruct_flex_t t' in
                         (match uu____12767 with
                          | (uu____12804,u1,k1,uu____12807) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12866 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12866 in
                              let sol =
                                let uu____12870 =
                                  let uu____12879 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12879) in
                                TERM uu____12870 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____13015 = pat_var_opt env pat_args hd1 in
                    (match uu____13015 with
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
                                    (fun uu____13078  ->
                                       match uu____13078 with
                                       | (x,uu____13084) ->
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
                            let uu____13099 =
                              let uu____13100 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____13100 in
                            if uu____13099
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____13112 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____13112 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____13127::uu____13128) ->
                    let uu____13159 =
                      let uu____13172 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13172 in
                    (match uu____13159 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13211 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13218::uu____13219,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13254 =
                let uu____13267 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13267 in
              (match uu____13254 with
               | (all_formals,res_t) ->
                   let uu____13292 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13292 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13326 = lhs in
          match uu____13326 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13336 ->
                    let uu____13337 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13337 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13360 = p in
          match uu____13360 with
          | (((u,k),xs,c),ps,(h,uu____13371,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13453 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13453 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13476 = h gs_xs in
                     let uu____13477 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_58  -> FStar_Pervasives_Native.Some _0_58) in
                     FStar_Syntax_Util.abs xs1 uu____13476 uu____13477 in
                   ((let uu____13483 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13483
                     then
                       let uu____13484 =
                         let uu____13487 =
                           let uu____13488 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13488
                             (FStar_String.concat "\n\t") in
                         let uu____13493 =
                           let uu____13496 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13497 =
                             let uu____13500 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13501 =
                               let uu____13504 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13505 =
                                 let uu____13508 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13509 =
                                   let uu____13512 =
                                     let uu____13513 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13513
                                       (FStar_String.concat ", ") in
                                   let uu____13518 =
                                     let uu____13521 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13521] in
                                   uu____13512 :: uu____13518 in
                                 uu____13508 :: uu____13509 in
                               uu____13504 :: uu____13505 in
                             uu____13500 :: uu____13501 in
                           uu____13496 :: uu____13497 in
                         uu____13487 :: uu____13493 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13484
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___161_13542 =
          match uu___161_13542 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13574 = p in
          match uu____13574 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13665 = FStar_List.nth ps i in
              (match uu____13665 with
               | (pi,uu____13669) ->
                   let uu____13674 = FStar_List.nth xs i in
                   (match uu____13674 with
                    | (xi,uu____13686) ->
                        let rec gs k =
                          let uu____13699 =
                            let uu____13712 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13712 in
                          match uu____13699 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13787)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13800 = new_uvar r xs k_a in
                                    (match uu____13800 with
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
                                         let uu____13822 = aux subst2 tl1 in
                                         (match uu____13822 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13849 =
                                                let uu____13852 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13852 :: gi_xs' in
                                              let uu____13853 =
                                                let uu____13856 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13856 :: gi_ps' in
                                              (uu____13849, uu____13853))) in
                              aux [] bs in
                        let uu____13861 =
                          let uu____13862 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13862 in
                        if uu____13861
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13866 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13866 with
                           | (g_xs,uu____13878) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13889 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13890 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_59  ->
                                        FStar_Pervasives_Native.Some _0_59) in
                                 FStar_Syntax_Util.abs xs uu____13889
                                   uu____13890 in
                               let sub1 =
                                 let uu____13896 =
                                   let uu____13901 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13904 =
                                     let uu____13907 =
                                       FStar_List.map
                                         (fun uu____13922  ->
                                            match uu____13922 with
                                            | (uu____13931,uu____13932,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13907 in
                                   mk_problem (p_scope orig) orig uu____13901
                                     (p_rel orig) uu____13904
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_TypeChecker_Common.TProb _0_60)
                                   uu____13896 in
                               ((let uu____13947 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13947
                                 then
                                   let uu____13948 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13949 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13948 uu____13949
                                 else ());
                                (let wl2 =
                                   let uu____13952 =
                                     let uu____13955 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13955 in
                                   solve_prob orig uu____13952
                                     [TERM (u, proj)] wl1 in
                                 let uu____13964 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_Pervasives_Native.Some _0_61)
                                   uu____13964))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13995 = lhs in
          match uu____13995 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14031 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14031 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14064 =
                        let uu____14111 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14111) in
                      FStar_Pervasives_Native.Some uu____14064
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14255 =
                           let uu____14262 =
                             let uu____14263 = FStar_Syntax_Subst.compress k1 in
                             uu____14263.FStar_Syntax_Syntax.n in
                           (uu____14262, args) in
                         match uu____14255 with
                         | (uu____14274,[]) ->
                             let uu____14277 =
                               let uu____14288 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14288) in
                             FStar_Pervasives_Native.Some uu____14277
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14309,uu____14310) ->
                             let uu____14331 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14331 with
                              | (uv1,uv_args) ->
                                  let uu____14374 =
                                    let uu____14375 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14375.FStar_Syntax_Syntax.n in
                                  (match uu____14374 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14385) ->
                                       let uu____14410 =
                                         pat_vars env [] uv_args in
                                       (match uu____14410 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14437  ->
                                                      let uu____14438 =
                                                        let uu____14439 =
                                                          let uu____14440 =
                                                            let uu____14445 =
                                                              let uu____14446
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14446
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14445 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14440 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14439 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14438)) in
                                            let c1 =
                                              let uu____14456 =
                                                let uu____14457 =
                                                  let uu____14462 =
                                                    let uu____14463 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14463
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14462 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14457 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14456 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14476 =
                                                let uu____14479 =
                                                  let uu____14480 =
                                                    let uu____14483 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14483
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14480 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14479 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14476 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14501 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14506,uu____14507) ->
                             let uu____14526 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14526 with
                              | (uv1,uv_args) ->
                                  let uu____14569 =
                                    let uu____14570 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14570.FStar_Syntax_Syntax.n in
                                  (match uu____14569 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14580) ->
                                       let uu____14605 =
                                         pat_vars env [] uv_args in
                                       (match uu____14605 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14632  ->
                                                      let uu____14633 =
                                                        let uu____14634 =
                                                          let uu____14635 =
                                                            let uu____14640 =
                                                              let uu____14641
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14641
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14640 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14635 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14634 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14633)) in
                                            let c1 =
                                              let uu____14651 =
                                                let uu____14652 =
                                                  let uu____14657 =
                                                    let uu____14658 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14658
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14657 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14652 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14651 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14671 =
                                                let uu____14674 =
                                                  let uu____14675 =
                                                    let uu____14678 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14678
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14675 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14674 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14671 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14696 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14703) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14744 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14744
                                 (fun _0_62  ->
                                    FStar_Pervasives_Native.Some _0_62)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14780 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14780 with
                                  | (args1,rest) ->
                                      let uu____14809 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14809 with
                                       | (xs2,c2) ->
                                           let uu____14822 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14822
                                             (fun uu____14846  ->
                                                match uu____14846 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14886 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14886 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14954 =
                                        let uu____14959 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14959 in
                                      FStar_All.pipe_right uu____14954
                                        (fun _0_63  ->
                                           FStar_Pervasives_Native.Some _0_63))
                         | uu____14974 ->
                             let uu____14981 =
                               let uu____14982 =
                                 let uu____14987 =
                                   let uu____14988 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14989 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14990 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14988 uu____14989 uu____14990 in
                                 (uu____14987, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14982 in
                             FStar_Exn.raise uu____14981 in
                       let uu____14997 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14997
                         (fun uu____15052  ->
                            match uu____15052 with
                            | (xs1,c1) ->
                                let uu____15101 =
                                  let uu____15142 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15142) in
                                FStar_Pervasives_Native.Some uu____15101)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15263 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15279 = project orig env wl1 i st in
                     match uu____15279 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15293) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15308 = imitate orig env wl1 st in
                  match uu____15308 with
                  | Failed uu____15313 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15344 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15344 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15369 =
                      let uu____15370 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15370 wl2 in
                    (match uu____15369 with
                     | Failed uu____15371 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15389 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15389 with
                | (hd1,uu____15405) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15426 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15439 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15440 -> true
                     | uu____15457 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15461 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15461
                         then true
                         else
                           ((let uu____15464 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15464
                             then
                               let uu____15465 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15465
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15485 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15485 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15498 =
                            let uu____15499 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15499 in
                          giveup_or_defer1 orig uu____15498
                        else
                          (let uu____15501 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15501
                           then
                             let uu____15502 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15502
                              then
                                let uu____15503 = subterms args_lhs in
                                imitate' orig env wl1 uu____15503
                              else
                                ((let uu____15508 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15508
                                  then
                                    let uu____15509 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15510 = names_to_string fvs1 in
                                    let uu____15511 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15509 uu____15510 uu____15511
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
                               (let uu____15515 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15515
                                then
                                  ((let uu____15517 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15517
                                    then
                                      let uu____15518 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15519 = names_to_string fvs1 in
                                      let uu____15520 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15518 uu____15519 uu____15520
                                    else ());
                                   (let uu____15522 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15522))
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
                     (let uu____15533 =
                        let uu____15534 = FStar_Syntax_Free.names t1 in
                        check_head uu____15534 t2 in
                      if uu____15533
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15545 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15545
                          then
                            let uu____15546 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15547 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15546 uu____15547
                          else ());
                         (let uu____15555 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15555))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15632 uu____15633 r =
               match (uu____15632, uu____15633) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15831 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15831
                   then
                     let uu____15832 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15832
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15856 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15856
                       then
                         let uu____15857 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15858 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15859 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15860 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15861 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15857 uu____15858 uu____15859 uu____15860
                           uu____15861
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15921 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15921 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15935 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15935 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15989 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15989 in
                                  let uu____15992 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15992 k3)
                           else
                             (let uu____15996 =
                                let uu____15997 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15998 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15999 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15997 uu____15998 uu____15999 in
                              failwith uu____15996) in
                       let uu____16000 =
                         let uu____16007 =
                           let uu____16020 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16020 in
                         match uu____16007 with
                         | (bs,k1') ->
                             let uu____16045 =
                               let uu____16058 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16058 in
                             (match uu____16045 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16086 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_64  ->
                                         FStar_TypeChecker_Common.TProb _0_64)
                                      uu____16086 in
                                  let uu____16095 =
                                    let uu____16100 =
                                      let uu____16101 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16101.FStar_Syntax_Syntax.n in
                                    let uu____16104 =
                                      let uu____16105 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16105.FStar_Syntax_Syntax.n in
                                    (uu____16100, uu____16104) in
                                  (match uu____16095 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16114,uu____16115) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16118,FStar_Syntax_Syntax.Tm_type
                                      uu____16119) -> (k2'_ys, [sub_prob])
                                   | uu____16122 ->
                                       let uu____16127 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16127 with
                                        | (t,uu____16139) ->
                                            let uu____16140 = new_uvar r zs t in
                                            (match uu____16140 with
                                             | (k_zs,uu____16152) ->
                                                 let kprob =
                                                   let uu____16154 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_65  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_65) uu____16154 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16000 with
                       | (k_u',sub_probs) ->
                           let uu____16171 =
                             let uu____16182 =
                               let uu____16183 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16183 in
                             let uu____16192 =
                               let uu____16195 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16195 in
                             let uu____16198 =
                               let uu____16201 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16201 in
                             (uu____16182, uu____16192, uu____16198) in
                           (match uu____16171 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16220 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16220 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16239 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16239
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16243 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16243 with
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
             let solve_one_pat uu____16296 uu____16297 =
               match (uu____16296, uu____16297) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16415 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16415
                     then
                       let uu____16416 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16417 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16416 uu____16417
                     else ());
                    (let uu____16419 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16419
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16438  ->
                              fun uu____16439  ->
                                match (uu____16438, uu____16439) with
                                | ((a,uu____16457),(t21,uu____16459)) ->
                                    let uu____16468 =
                                      let uu____16473 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16473
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16468
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66))
                           xs args2 in
                       let guard =
                         let uu____16479 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16479 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16494 = occurs_check env wl (u1, k1) t21 in
                        match uu____16494 with
                        | (occurs_ok,uu____16502) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16510 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16510
                            then
                              let sol =
                                let uu____16512 =
                                  let uu____16521 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16521) in
                                TERM uu____16512 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16528 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16528
                               then
                                 let uu____16529 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16529 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16553,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16579 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16579
                                       then
                                         let uu____16580 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16580
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16587 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16589 = lhs in
             match uu____16589 with
             | (t1,u1,k1,args1) ->
                 let uu____16594 = rhs in
                 (match uu____16594 with
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
                       | uu____16634 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16644 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16644 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16662) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16669 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16669
                                    then
                                      let uu____16670 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16670
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16677 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16679 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16679
        then
          let uu____16680 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16680
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16684 = FStar_Util.physical_equality t1 t2 in
           if uu____16684
           then
             let uu____16685 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16685
           else
             ((let uu____16688 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16688
               then
                 let uu____16689 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16689
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16692,uu____16693) ->
                   let uu____16720 =
                     let uu___197_16721 = problem in
                     let uu____16722 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16721.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16722;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16721.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16721.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16721.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16721.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16721.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16721.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16721.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16721.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16720 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16723,uu____16724) ->
                   let uu____16731 =
                     let uu___197_16732 = problem in
                     let uu____16733 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16732.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16733;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16732.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16732.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16732.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16732.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16732.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16732.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16732.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16732.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16731 wl
               | (uu____16734,FStar_Syntax_Syntax.Tm_ascribed uu____16735) ->
                   let uu____16762 =
                     let uu___198_16763 = problem in
                     let uu____16764 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16763.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16763.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16763.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16764;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16763.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16763.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16763.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16763.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16763.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16763.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16762 wl
               | (uu____16765,FStar_Syntax_Syntax.Tm_meta uu____16766) ->
                   let uu____16773 =
                     let uu___198_16774 = problem in
                     let uu____16775 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16774.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16774.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16774.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16775;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16774.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16774.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16774.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16774.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16774.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16774.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16773 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16776,uu____16777) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16778,FStar_Syntax_Syntax.Tm_bvar uu____16779) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___162_16834 =
                     match uu___162_16834 with
                     | [] -> c
                     | bs ->
                         let uu____16856 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16856 in
                   let uu____16865 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16865 with
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
                                   let uu____17007 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17007
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17009 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.CProb _0_67)
                                   uu____17009))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___163_17085 =
                     match uu___163_17085 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17119 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17119 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17255 =
                                   let uu____17260 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17261 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17260
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17261 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.TProb _0_68)
                                   uu____17255))
               | (FStar_Syntax_Syntax.Tm_abs uu____17266,uu____17267) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17292 -> true
                     | uu____17309 -> false in
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
                       (let uu____17356 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17364 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17364.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17364.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17364.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17364.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17364.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17364.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17364.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17364.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17364.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17364.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17364.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17364.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17364.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17364.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17364.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17364.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17364.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17364.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17364.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17364.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17364.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17364.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17364.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17364.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17364.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17364.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17364.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17364.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17364.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17364.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17356 with
                        | (uu____17367,ty,uu____17369) ->
                            let uu____17370 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17370) in
                   let uu____17371 =
                     let uu____17388 = maybe_eta t1 in
                     let uu____17395 = maybe_eta t2 in
                     (uu____17388, uu____17395) in
                   (match uu____17371 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17437 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17437.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17437.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17437.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17437.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17437.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17437.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17437.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17437.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17460 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17460
                        then
                          let uu____17461 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17461 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17476 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17476.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17476.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17476.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17476.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17476.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17476.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17476.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17476.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17500 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17500
                        then
                          let uu____17501 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17501 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17516 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17516.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17516.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17516.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17516.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17516.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17516.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17516.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17516.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17520 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17537,FStar_Syntax_Syntax.Tm_abs uu____17538) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17563 -> true
                     | uu____17580 -> false in
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
                       (let uu____17627 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17635 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17635.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17635.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17635.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17635.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17635.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17635.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17635.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17635.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17635.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17635.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17635.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17635.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17635.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17635.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17635.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17635.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17635.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17635.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17635.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17635.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17635.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17635.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17635.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17635.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17635.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17635.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17635.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17635.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17635.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17635.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17627 with
                        | (uu____17638,ty,uu____17640) ->
                            let uu____17641 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17641) in
                   let uu____17642 =
                     let uu____17659 = maybe_eta t1 in
                     let uu____17666 = maybe_eta t2 in
                     (uu____17659, uu____17666) in
                   (match uu____17642 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17708 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17708.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17708.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17708.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17708.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17708.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17708.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17708.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17708.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17731 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17731
                        then
                          let uu____17732 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17732 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17747 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17747.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17747.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17747.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17747.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17747.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17747.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17747.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17747.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17771 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17771
                        then
                          let uu____17772 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17772 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17787 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17787.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17787.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17787.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17787.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17787.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17787.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17787.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17787.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17791 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17808,FStar_Syntax_Syntax.Tm_refine uu____17809) ->
                   let uu____17822 = as_refinement env wl t1 in
                   (match uu____17822 with
                    | (x1,phi1) ->
                        let uu____17829 = as_refinement env wl t2 in
                        (match uu____17829 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17837 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_69  ->
                                    FStar_TypeChecker_Common.TProb _0_69)
                                 uu____17837 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17875 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17875
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17879 =
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
                                 let uu____17885 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17885 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17894 =
                                   let uu____17899 =
                                     let uu____17900 =
                                       let uu____17907 =
                                         FStar_Syntax_Syntax.mk_binder x11 in
                                       [uu____17907] in
                                     FStar_List.append (p_scope orig)
                                       uu____17900 in
                                   mk_problem uu____17899 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_70  ->
                                      FStar_TypeChecker_Common.TProb _0_70)
                                   uu____17894 in
                               let uu____17916 =
                                 solve env1
                                   (let uu___202_17918 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___202_17918.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___202_17918.smt_ok);
                                      tcenv = (uu___202_17918.tcenv)
                                    }) in
                               (match uu____17916 with
                                | Failed uu____17925 -> fallback ()
                                | Success uu____17930 ->
                                    let guard =
                                      let uu____17934 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17939 =
                                        let uu____17940 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17940
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17934
                                        uu____17939 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___203_17949 = wl1 in
                                      {
                                        attempting =
                                          (uu___203_17949.attempting);
                                        wl_deferred =
                                          (uu___203_17949.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___203_17949.defer_ok);
                                        smt_ok = (uu___203_17949.smt_ok);
                                        tcenv = (uu___203_17949.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17951,FStar_Syntax_Syntax.Tm_uvar uu____17952) ->
                   let uu____17985 = destruct_flex_t t1 in
                   let uu____17986 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17985 uu____17986
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17987;
                     FStar_Syntax_Syntax.pos = uu____17988;
                     FStar_Syntax_Syntax.vars = uu____17989;_},uu____17990),FStar_Syntax_Syntax.Tm_uvar
                  uu____17991) ->
                   let uu____18044 = destruct_flex_t t1 in
                   let uu____18045 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18044 uu____18045
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18046,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18047;
                     FStar_Syntax_Syntax.pos = uu____18048;
                     FStar_Syntax_Syntax.vars = uu____18049;_},uu____18050))
                   ->
                   let uu____18103 = destruct_flex_t t1 in
                   let uu____18104 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18103 uu____18104
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18105;
                     FStar_Syntax_Syntax.pos = uu____18106;
                     FStar_Syntax_Syntax.vars = uu____18107;_},uu____18108),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18109;
                     FStar_Syntax_Syntax.pos = uu____18110;
                     FStar_Syntax_Syntax.vars = uu____18111;_},uu____18112))
                   ->
                   let uu____18185 = destruct_flex_t t1 in
                   let uu____18186 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18185 uu____18186
               | (FStar_Syntax_Syntax.Tm_uvar uu____18187,uu____18188) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18205 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18205 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18212;
                     FStar_Syntax_Syntax.pos = uu____18213;
                     FStar_Syntax_Syntax.vars = uu____18214;_},uu____18215),uu____18216)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18253 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18253 t2 wl
               | (uu____18260,FStar_Syntax_Syntax.Tm_uvar uu____18261) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18278,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18279;
                     FStar_Syntax_Syntax.pos = uu____18280;
                     FStar_Syntax_Syntax.vars = uu____18281;_},uu____18282))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18319,FStar_Syntax_Syntax.Tm_type uu____18320) ->
                   solve_t' env
                     (let uu___204_18338 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18338.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18338.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18338.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18338.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18338.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18338.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18338.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18338.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18338.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18339;
                     FStar_Syntax_Syntax.pos = uu____18340;
                     FStar_Syntax_Syntax.vars = uu____18341;_},uu____18342),FStar_Syntax_Syntax.Tm_type
                  uu____18343) ->
                   solve_t' env
                     (let uu___204_18381 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18381.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18381.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18381.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18381.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18381.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18381.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18381.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18381.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18381.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18382,FStar_Syntax_Syntax.Tm_arrow uu____18383) ->
                   solve_t' env
                     (let uu___204_18413 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18413.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18413.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18413.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18413.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18413.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18413.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18413.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18413.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18413.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18414;
                     FStar_Syntax_Syntax.pos = uu____18415;
                     FStar_Syntax_Syntax.vars = uu____18416;_},uu____18417),FStar_Syntax_Syntax.Tm_arrow
                  uu____18418) ->
                   solve_t' env
                     (let uu___204_18468 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18468.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18468.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18468.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18468.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18468.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18468.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18468.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18468.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18468.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18469,uu____18470) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18489 =
                        let uu____18490 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18490 in
                      if uu____18489
                      then
                        let uu____18491 =
                          FStar_All.pipe_left
                            (fun _0_71  ->
                               FStar_TypeChecker_Common.TProb _0_71)
                            (let uu___205_18497 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18497.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18497.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18497.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18497.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18497.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18497.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18497.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18497.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18497.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18498 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18491 uu____18498 t2
                          wl
                      else
                        (let uu____18506 = base_and_refinement env wl t2 in
                         match uu____18506 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18549 =
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      (let uu___206_18555 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18555.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18555.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18555.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18555.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18555.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18555.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18555.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18555.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18555.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18556 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18549
                                    uu____18556 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18576 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18576.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18576.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18579 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      uu____18579 in
                                  let guard =
                                    let uu____18591 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18591
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18599;
                     FStar_Syntax_Syntax.pos = uu____18600;
                     FStar_Syntax_Syntax.vars = uu____18601;_},uu____18602),uu____18603)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18642 =
                        let uu____18643 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18643 in
                      if uu____18642
                      then
                        let uu____18644 =
                          FStar_All.pipe_left
                            (fun _0_74  ->
                               FStar_TypeChecker_Common.TProb _0_74)
                            (let uu___205_18650 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18650.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18650.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18650.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18650.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18650.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18650.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18650.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18650.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18650.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18651 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18644 uu____18651 t2
                          wl
                      else
                        (let uu____18659 = base_and_refinement env wl t2 in
                         match uu____18659 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18702 =
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      (let uu___206_18708 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18708.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18708.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18708.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18708.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18708.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18708.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18708.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18708.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18708.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18709 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18702
                                    uu____18709 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18729 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18729.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18729.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18732 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      uu____18732 in
                                  let guard =
                                    let uu____18744 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18744
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18752,FStar_Syntax_Syntax.Tm_uvar uu____18753) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18771 = base_and_refinement env wl t1 in
                      match uu____18771 with
                      | (t_base,uu____18787) ->
                          solve_t env
                            (let uu___208_18809 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_18809.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_18809.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_18809.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_18809.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_18809.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_18809.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_18809.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_18809.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18812,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18813;
                     FStar_Syntax_Syntax.pos = uu____18814;
                     FStar_Syntax_Syntax.vars = uu____18815;_},uu____18816))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18854 = base_and_refinement env wl t1 in
                      match uu____18854 with
                      | (t_base,uu____18870) ->
                          solve_t env
                            (let uu___208_18892 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_18892.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_18892.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_18892.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_18892.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_18892.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_18892.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_18892.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_18892.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18895,uu____18896) ->
                   let t21 =
                     let uu____18906 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18906 in
                   solve_t env
                     (let uu___209_18930 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___209_18930.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___209_18930.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___209_18930.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___209_18930.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___209_18930.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___209_18930.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___209_18930.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___209_18930.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___209_18930.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18931,FStar_Syntax_Syntax.Tm_refine uu____18932) ->
                   let t11 =
                     let uu____18942 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18942 in
                   solve_t env
                     (let uu___210_18966 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___210_18966.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___210_18966.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___210_18966.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___210_18966.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___210_18966.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___210_18966.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___210_18966.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___210_18966.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___210_18966.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18969,uu____18970) ->
                   let head1 =
                     let uu____18996 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18996
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19040 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19040
                       FStar_Pervasives_Native.fst in
                   let uu____19081 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19081
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19096 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19096
                      then
                        let guard =
                          let uu____19108 =
                            let uu____19109 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19109 = FStar_Syntax_Util.Equal in
                          if uu____19108
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19113 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____19113) in
                        let uu____19116 = solve_prob orig guard [] wl in
                        solve env uu____19116
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19119,uu____19120) ->
                   let head1 =
                     let uu____19130 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19130
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19174 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19174
                       FStar_Pervasives_Native.fst in
                   let uu____19215 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19215
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19230 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19230
                      then
                        let guard =
                          let uu____19242 =
                            let uu____19243 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19243 = FStar_Syntax_Util.Equal in
                          if uu____19242
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19247 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19247) in
                        let uu____19250 = solve_prob orig guard [] wl in
                        solve env uu____19250
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19253,uu____19254) ->
                   let head1 =
                     let uu____19258 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19258
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19302 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19302
                       FStar_Pervasives_Native.fst in
                   let uu____19343 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19343
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19358 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19358
                      then
                        let guard =
                          let uu____19370 =
                            let uu____19371 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19371 = FStar_Syntax_Util.Equal in
                          if uu____19370
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19375 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19375) in
                        let uu____19378 = solve_prob orig guard [] wl in
                        solve env uu____19378
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19381,uu____19382) ->
                   let head1 =
                     let uu____19386 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19386
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19430 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19430
                       FStar_Pervasives_Native.fst in
                   let uu____19471 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19471
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19486 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19486
                      then
                        let guard =
                          let uu____19498 =
                            let uu____19499 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19499 = FStar_Syntax_Util.Equal in
                          if uu____19498
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19503 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19503) in
                        let uu____19506 = solve_prob orig guard [] wl in
                        solve env uu____19506
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19509,uu____19510) ->
                   let head1 =
                     let uu____19514 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19514
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19558 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19558
                       FStar_Pervasives_Native.fst in
                   let uu____19599 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19599
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19614 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19614
                      then
                        let guard =
                          let uu____19626 =
                            let uu____19627 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19627 = FStar_Syntax_Util.Equal in
                          if uu____19626
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19631 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19631) in
                        let uu____19634 = solve_prob orig guard [] wl in
                        solve env uu____19634
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19637,uu____19638) ->
                   let head1 =
                     let uu____19656 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19656
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19700 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19700
                       FStar_Pervasives_Native.fst in
                   let uu____19741 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19741
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19756 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19756
                      then
                        let guard =
                          let uu____19768 =
                            let uu____19769 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19769 = FStar_Syntax_Util.Equal in
                          if uu____19768
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19773 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19773) in
                        let uu____19776 = solve_prob orig guard [] wl in
                        solve env uu____19776
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19779,FStar_Syntax_Syntax.Tm_match uu____19780) ->
                   let head1 =
                     let uu____19806 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19806
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19850 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19850
                       FStar_Pervasives_Native.fst in
                   let uu____19891 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19891
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19906 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19906
                      then
                        let guard =
                          let uu____19918 =
                            let uu____19919 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19919 = FStar_Syntax_Util.Equal in
                          if uu____19918
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19923 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19923) in
                        let uu____19926 = solve_prob orig guard [] wl in
                        solve env uu____19926
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19929,FStar_Syntax_Syntax.Tm_uinst uu____19930) ->
                   let head1 =
                     let uu____19940 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19940
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19984 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19984
                       FStar_Pervasives_Native.fst in
                   let uu____20025 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20025
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20040 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20040
                      then
                        let guard =
                          let uu____20052 =
                            let uu____20053 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20053 = FStar_Syntax_Util.Equal in
                          if uu____20052
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20057 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20057) in
                        let uu____20060 = solve_prob orig guard [] wl in
                        solve env uu____20060
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20063,FStar_Syntax_Syntax.Tm_name uu____20064) ->
                   let head1 =
                     let uu____20068 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20068
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20112 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20112
                       FStar_Pervasives_Native.fst in
                   let uu____20153 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20153
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20168 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20168
                      then
                        let guard =
                          let uu____20180 =
                            let uu____20181 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20181 = FStar_Syntax_Util.Equal in
                          if uu____20180
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20185 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20185) in
                        let uu____20188 = solve_prob orig guard [] wl in
                        solve env uu____20188
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20191,FStar_Syntax_Syntax.Tm_constant uu____20192) ->
                   let head1 =
                     let uu____20196 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20196
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20240 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20240
                       FStar_Pervasives_Native.fst in
                   let uu____20281 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20281
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20296 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20296
                      then
                        let guard =
                          let uu____20308 =
                            let uu____20309 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20309 = FStar_Syntax_Util.Equal in
                          if uu____20308
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20313 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20313) in
                        let uu____20316 = solve_prob orig guard [] wl in
                        solve env uu____20316
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20319,FStar_Syntax_Syntax.Tm_fvar uu____20320) ->
                   let head1 =
                     let uu____20324 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20324
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20368 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20368
                       FStar_Pervasives_Native.fst in
                   let uu____20409 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20409
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20424 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20424
                      then
                        let guard =
                          let uu____20436 =
                            let uu____20437 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20437 = FStar_Syntax_Util.Equal in
                          if uu____20436
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20441 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20441) in
                        let uu____20444 = solve_prob orig guard [] wl in
                        solve env uu____20444
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20447,FStar_Syntax_Syntax.Tm_app uu____20448) ->
                   let head1 =
                     let uu____20466 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20466
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20510 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20510
                       FStar_Pervasives_Native.fst in
                   let uu____20551 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20551
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20566 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20566
                      then
                        let guard =
                          let uu____20578 =
                            let uu____20579 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20579 = FStar_Syntax_Util.Equal in
                          if uu____20578
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20583 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20583) in
                        let uu____20586 = solve_prob orig guard [] wl in
                        solve env uu____20586
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20589,uu____20590) ->
                   let uu____20603 =
                     let uu____20604 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20605 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20604
                       uu____20605 in
                   failwith uu____20603
               | (FStar_Syntax_Syntax.Tm_delayed uu____20606,uu____20607) ->
                   let uu____20632 =
                     let uu____20633 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20634 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20633
                       uu____20634 in
                   failwith uu____20632
               | (uu____20635,FStar_Syntax_Syntax.Tm_delayed uu____20636) ->
                   let uu____20661 =
                     let uu____20662 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20663 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20662
                       uu____20663 in
                   failwith uu____20661
               | (uu____20664,FStar_Syntax_Syntax.Tm_let uu____20665) ->
                   let uu____20678 =
                     let uu____20679 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20680 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20679
                       uu____20680 in
                   failwith uu____20678
               | uu____20681 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20717 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20717
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20719 =
               let uu____20720 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20721 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20720 uu____20721 in
             giveup env uu____20719 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20741  ->
                    fun uu____20742  ->
                      match (uu____20741, uu____20742) with
                      | ((a1,uu____20760),(a2,uu____20762)) ->
                          let uu____20771 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_89  ->
                               FStar_TypeChecker_Common.TProb _0_89)
                            uu____20771)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20781 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20781 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20805 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20812)::[] -> wp1
              | uu____20829 ->
                  let uu____20838 =
                    let uu____20839 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20839 in
                  failwith uu____20838 in
            let uu____20842 =
              let uu____20851 =
                let uu____20852 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20852 in
              [uu____20851] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20842;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20853 = lift_c1 () in solve_eq uu____20853 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___164_20859  ->
                       match uu___164_20859 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20860 -> false)) in
             let uu____20861 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20895)::uu____20896,(wp2,uu____20898)::uu____20899)
                   -> (wp1, wp2)
               | uu____20956 ->
                   let uu____20977 =
                     let uu____20978 =
                       let uu____20983 =
                         let uu____20984 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20985 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20984 uu____20985 in
                       (uu____20983, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20978 in
                   FStar_Exn.raise uu____20977 in
             match uu____20861 with
             | (wpc1,wpc2) ->
                 let uu____21004 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____21004
                 then
                   let uu____21007 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____21007 wl
                 else
                   (let uu____21011 =
                      let uu____21018 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____21018 in
                    match uu____21011 with
                    | (c2_decl,qualifiers) ->
                        let uu____21039 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21039
                        then
                          let c1_repr =
                            let uu____21043 =
                              let uu____21044 =
                                let uu____21045 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21045 in
                              let uu____21046 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21044 uu____21046 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21043 in
                          let c2_repr =
                            let uu____21048 =
                              let uu____21049 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21050 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21049 uu____21050 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21048 in
                          let prob =
                            let uu____21052 =
                              let uu____21057 =
                                let uu____21058 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21059 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21058
                                  uu____21059 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21057 in
                            FStar_TypeChecker_Common.TProb uu____21052 in
                          let wl1 =
                            let uu____21061 =
                              let uu____21064 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21064 in
                            solve_prob orig uu____21061 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21073 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21073
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____21075 =
                                     let uu____21078 =
                                       let uu____21079 =
                                         let uu____21094 =
                                           let uu____21095 =
                                             let uu____21096 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____21096] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____21095 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21097 =
                                           let uu____21100 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21101 =
                                             let uu____21104 =
                                               let uu____21105 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21105 in
                                             [uu____21104] in
                                           uu____21100 :: uu____21101 in
                                         (uu____21094, uu____21097) in
                                       FStar_Syntax_Syntax.Tm_app uu____21079 in
                                     FStar_Syntax_Syntax.mk uu____21078 in
                                   uu____21075 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____21112 =
                                    let uu____21115 =
                                      let uu____21116 =
                                        let uu____21131 =
                                          let uu____21132 =
                                            let uu____21133 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____21133] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____21132 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21134 =
                                          let uu____21137 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21138 =
                                            let uu____21141 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21142 =
                                              let uu____21145 =
                                                let uu____21146 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21146 in
                                              [uu____21145] in
                                            uu____21141 :: uu____21142 in
                                          uu____21137 :: uu____21138 in
                                        (uu____21131, uu____21134) in
                                      FStar_Syntax_Syntax.Tm_app uu____21116 in
                                    FStar_Syntax_Syntax.mk uu____21115 in
                                  uu____21112 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21153 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_90  ->
                                  FStar_TypeChecker_Common.TProb _0_90)
                               uu____21153 in
                           let wl1 =
                             let uu____21163 =
                               let uu____21166 =
                                 let uu____21169 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21169 g in
                               FStar_All.pipe_left
                                 (fun _0_91  ->
                                    FStar_Pervasives_Native.Some _0_91)
                                 uu____21166 in
                             solve_prob orig uu____21163 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21182 = FStar_Util.physical_equality c1 c2 in
        if uu____21182
        then
          let uu____21183 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21183
        else
          ((let uu____21186 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21186
            then
              let uu____21187 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21188 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21187
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21188
            else ());
           (let uu____21190 =
              let uu____21195 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21196 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21195, uu____21196) in
            match uu____21190 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21200),FStar_Syntax_Syntax.Total
                    (t2,uu____21202)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21219 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21219 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21222,FStar_Syntax_Syntax.Total uu____21223) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21241),FStar_Syntax_Syntax.Total
                    (t2,uu____21243)) ->
                     let uu____21260 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21260 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21264),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21266)) ->
                     let uu____21283 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21283 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21287),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21289)) ->
                     let uu____21306 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21306 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21309,FStar_Syntax_Syntax.Comp uu____21310) ->
                     let uu____21319 =
                       let uu___211_21324 = problem in
                       let uu____21329 =
                         let uu____21330 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21330 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21324.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21329;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21324.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21324.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21324.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21324.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21324.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21324.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21324.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21324.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21319 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21331,FStar_Syntax_Syntax.Comp uu____21332) ->
                     let uu____21341 =
                       let uu___211_21346 = problem in
                       let uu____21351 =
                         let uu____21352 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21352 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21346.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21351;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21346.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21346.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21346.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21346.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21346.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21346.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21346.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21346.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21341 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21353,FStar_Syntax_Syntax.GTotal uu____21354) ->
                     let uu____21363 =
                       let uu___212_21368 = problem in
                       let uu____21373 =
                         let uu____21374 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21374 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21368.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21368.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21368.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21373;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21368.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21368.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21368.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21368.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21368.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21368.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21363 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21375,FStar_Syntax_Syntax.Total uu____21376) ->
                     let uu____21385 =
                       let uu___212_21390 = problem in
                       let uu____21395 =
                         let uu____21396 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21396 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21390.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21390.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21390.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21395;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21390.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21390.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21390.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21390.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21390.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21390.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21385 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21397,FStar_Syntax_Syntax.Comp uu____21398) ->
                     let uu____21399 =
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
                     if uu____21399
                     then
                       let uu____21400 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21400 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21406 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21416 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21417 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21416, uu____21417)) in
                          match uu____21406 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21424 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21424
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21426 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21426 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21429 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21431 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21431) in
                                if uu____21429
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
                                  (let uu____21434 =
                                     let uu____21435 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21436 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21435 uu____21436 in
                                   giveup env uu____21434 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21442 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21480  ->
              match uu____21480 with
              | (uu____21493,uu____21494,u,uu____21496,uu____21497,uu____21498)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21442 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21530 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21530 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21548 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21576  ->
                match uu____21576 with
                | (u1,u2) ->
                    let uu____21583 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21584 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21583 uu____21584)) in
      FStar_All.pipe_right uu____21548 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21603,[])) -> "{}"
      | uu____21628 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21645 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21645
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21648 =
              FStar_List.map
                (fun uu____21658  ->
                   match uu____21658 with
                   | (uu____21663,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21648 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21668 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21668 imps
let new_t_problem:
  'Auu____21683 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21683 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21683)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21717 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21717
                then
                  let uu____21718 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21719 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21718
                    (rel_to_string rel) uu____21719
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
            let uu____21747 =
              let uu____21750 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21750 in
            FStar_Syntax_Syntax.new_bv uu____21747 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21759 =
              let uu____21762 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21762 in
            let uu____21765 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21759 uu____21765 in
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
          let uu____21798 = FStar_Options.eager_inference () in
          if uu____21798
          then
            let uu___213_21799 = probs in
            {
              attempting = (uu___213_21799.attempting);
              wl_deferred = (uu___213_21799.wl_deferred);
              ctr = (uu___213_21799.ctr);
              defer_ok = false;
              smt_ok = (uu___213_21799.smt_ok);
              tcenv = (uu___213_21799.tcenv)
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
             (let uu____21811 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21811
              then
                let uu____21812 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21812
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
          ((let uu____21824 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21824
            then
              let uu____21825 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21825
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21829 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21829
             then
               let uu____21830 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21830
             else ());
            (let f2 =
               let uu____21833 =
                 let uu____21834 = FStar_Syntax_Util.unmeta f1 in
                 uu____21834.FStar_Syntax_Syntax.n in
               match uu____21833 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21838 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___214_21839 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___214_21839.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___214_21839.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___214_21839.FStar_TypeChecker_Env.implicits)
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
            let uu____21861 =
              let uu____21862 =
                let uu____21863 =
                  let uu____21864 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21864
                    (fun _0_94  -> FStar_TypeChecker_Common.NonTrivial _0_94) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21863;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21862 in
            FStar_All.pipe_left
              (fun _0_95  -> FStar_Pervasives_Native.Some _0_95) uu____21861
let with_guard_no_simp:
  'Auu____21895 .
    'Auu____21895 ->
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
            let uu____21915 =
              let uu____21916 =
                let uu____21917 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21917
                  (fun _0_96  -> FStar_TypeChecker_Common.NonTrivial _0_96) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21916;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21915
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
          (let uu____21959 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21959
           then
             let uu____21960 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21961 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21960
               uu____21961
           else ());
          (let prob =
             let uu____21964 =
               let uu____21969 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21969 in
             FStar_All.pipe_left
               (fun _0_97  -> FStar_TypeChecker_Common.TProb _0_97)
               uu____21964 in
           let g =
             let uu____21977 =
               let uu____21980 = singleton' env prob smt_ok in
               solve_and_commit env uu____21980
                 (fun uu____21982  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21977 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22003 = try_teq true env t1 t2 in
        match uu____22003 with
        | FStar_Pervasives_Native.None  ->
            let uu____22006 =
              let uu____22007 =
                let uu____22012 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____22013 = FStar_TypeChecker_Env.get_range env in
                (uu____22012, uu____22013) in
              FStar_Errors.Error uu____22007 in
            FStar_Exn.raise uu____22006
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22016 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____22016
              then
                let uu____22017 = FStar_Syntax_Print.term_to_string t1 in
                let uu____22018 = FStar_Syntax_Print.term_to_string t2 in
                let uu____22019 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22017
                  uu____22018 uu____22019
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
          (let uu____22040 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____22040
           then
             let uu____22041 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____22042 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____22041
               uu____22042
           else ());
          (let uu____22044 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____22044 with
           | (prob,x) ->
               let g =
                 let uu____22056 =
                   let uu____22059 = singleton' env prob smt_ok in
                   solve_and_commit env uu____22059
                     (fun uu____22061  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____22056 in
               ((let uu____22071 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____22071
                 then
                   let uu____22072 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____22073 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____22074 =
                     let uu____22075 = FStar_Util.must g in
                     guard_to_string env uu____22075 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____22072 uu____22073 uu____22074
                 else ());
                (let uu____22077 =
                   let uu____22080 = FStar_Syntax_Syntax.mk_binder x in
                   abstract_guard uu____22080 in
                 FStar_Util.map_opt g uu____22077)))
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
          let uu____22111 = FStar_TypeChecker_Env.get_range env in
          let uu____22112 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____22111 uu____22112
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22128 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22128
         then
           let uu____22129 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22130 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22129
             uu____22130
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22135 =
             let uu____22140 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22140 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_98  -> FStar_TypeChecker_Common.CProb _0_98) uu____22135 in
         let uu____22145 =
           let uu____22148 = singleton env prob in
           solve_and_commit env uu____22148
             (fun uu____22150  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22145)
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
      fun uu____22182  ->
        match uu____22182 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22221 =
                 let uu____22222 =
                   let uu____22227 =
                     let uu____22228 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22229 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22228 uu____22229 in
                   let uu____22230 = FStar_TypeChecker_Env.get_range env in
                   (uu____22227, uu____22230) in
                 FStar_Errors.Error uu____22222 in
               FStar_Exn.raise uu____22221) in
            let equiv1 v1 v' =
              let uu____22238 =
                let uu____22243 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22244 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22243, uu____22244) in
              match uu____22238 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22263 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22293 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22293 with
                      | FStar_Syntax_Syntax.U_unif uu____22300 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22329  ->
                                    match uu____22329 with
                                    | (u,v') ->
                                        let uu____22338 = equiv1 v1 v' in
                                        if uu____22338
                                        then
                                          let uu____22341 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22341 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22357 -> [])) in
            let uu____22362 =
              let wl =
                let uu___215_22366 = empty_worklist env in
                {
                  attempting = (uu___215_22366.attempting);
                  wl_deferred = (uu___215_22366.wl_deferred);
                  ctr = (uu___215_22366.ctr);
                  defer_ok = false;
                  smt_ok = (uu___215_22366.smt_ok);
                  tcenv = (uu___215_22366.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22384  ->
                      match uu____22384 with
                      | (lb,v1) ->
                          let uu____22391 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22391 with
                           | USolved wl1 -> ()
                           | uu____22393 -> fail lb v1))) in
            let rec check_ineq uu____22401 =
              match uu____22401 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22410) -> true
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
                      uu____22433,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22435,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22446) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22453,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22461 -> false) in
            let uu____22466 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22481  ->
                      match uu____22481 with
                      | (u,v1) ->
                          let uu____22488 = check_ineq (u, v1) in
                          if uu____22488
                          then true
                          else
                            ((let uu____22491 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22491
                              then
                                let uu____22492 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22493 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22492
                                  uu____22493
                              else ());
                             false))) in
            if uu____22466
            then ()
            else
              ((let uu____22497 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22497
                then
                  ((let uu____22499 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22499);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22509 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22509))
                else ());
               (let uu____22519 =
                  let uu____22520 =
                    let uu____22525 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22525) in
                  FStar_Errors.Error uu____22520 in
                FStar_Exn.raise uu____22519))
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
      let fail uu____22577 =
        match uu____22577 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22591 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22591
       then
         let uu____22592 = wl_to_string wl in
         let uu____22593 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22592 uu____22593
       else ());
      (let g1 =
         let uu____22608 = solve_and_commit env wl fail in
         match uu____22608 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___216_22621 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___216_22621.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___216_22621.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___216_22621.FStar_TypeChecker_Env.implicits)
             }
         | uu____22626 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___217_22630 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___217_22630.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___217_22630.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___217_22630.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22653 = FStar_ST.op_Bang last_proof_ns in
    match uu____22653 with
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
            let uu___218_22840 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___218_22840.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___218_22840.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___218_22840.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22841 =
            let uu____22842 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22842 in
          if uu____22841
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22850 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22850
                   then
                     let uu____22851 = FStar_TypeChecker_Env.get_range env in
                     let uu____22852 =
                       let uu____22853 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22853 in
                     FStar_Errors.diag uu____22851 uu____22852
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   (let uu____22857 =
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Norm"))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____22857
                    then
                      let uu____22858 = FStar_TypeChecker_Env.get_range env in
                      let uu____22859 =
                        let uu____22860 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22860 in
                      FStar_Errors.diag uu____22858 uu____22859
                    else ());
                   (let uu____22862 = check_trivial vc1 in
                    match uu____22862 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          ((let uu____22869 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____22869
                            then
                              let uu____22870 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22871 =
                                let uu____22872 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22872 in
                              FStar_Errors.diag uu____22870 uu____22871
                            else ());
                           FStar_Pervasives_Native.None)
                        else
                          ((let uu____22877 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____22877
                            then
                              let uu____22878 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22879 =
                                let uu____22880 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22880 in
                              FStar_Errors.diag uu____22878 uu____22879
                            else ());
                           (let vcs =
                              let uu____22891 = FStar_Options.use_tactics () in
                              if uu____22891
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22910  ->
                                     (let uu____22912 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22912);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22914 =
                                   let uu____22921 = FStar_Options.peek () in
                                   (env, vc2, uu____22921) in
                                 [uu____22914]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22955  ->
                                    match uu____22955 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22966 = check_trivial goal1 in
                                        (match uu____22966 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             let uu____22968 =
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel"))
                                                 ||
                                                 (FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env1)
                                                    (FStar_Options.Other
                                                       "Tac")) in
                                             if uu____22968
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal2 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              (let uu____22975 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Rel") in
                                               if uu____22975
                                               then
                                                 let uu____22976 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22977 =
                                                   let uu____22978 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22979 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22978 uu____22979 in
                                                 FStar_Errors.diag
                                                   uu____22976 uu____22977
                                               else ());
                                              (let uu____22982 =
                                                 (FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env1)
                                                    (FStar_Options.Other
                                                       "Norm"))
                                                   ||
                                                   (FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "SMTQuery")) in
                                               if uu____22982
                                               then
                                                 let uu____22983 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22984 =
                                                   let uu____22985 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22985 in
                                                 FStar_Errors.diag
                                                   uu____22983 uu____22984
                                               else ());
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal2;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
let discharge_guard_no_smt:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22997 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22997 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23003 =
            let uu____23004 =
              let uu____23009 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____23009) in
            FStar_Errors.Error uu____23004 in
          FStar_Exn.raise uu____23003
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____23018 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____23018 with
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
          let uu____23040 = FStar_Syntax_Unionfind.find u in
          match uu____23040 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23043 -> false in
        let rec until_fixpoint acc implicits =
          let uu____23061 = acc in
          match uu____23061 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23147 = hd1 in
                   (match uu____23147 with
                    | (uu____23160,env,u,tm,k,r) ->
                        let uu____23166 = unresolved u in
                        if uu____23166
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____23197 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23197
                            then
                              let uu____23198 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23199 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23200 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23198 uu____23199 uu____23200
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___219_23203 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___219_23203.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___219_23203.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___219_23203.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___219_23203.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___219_23203.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___219_23203.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___219_23203.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___219_23203.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___219_23203.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___219_23203.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___219_23203.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___219_23203.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___219_23203.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___219_23203.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___219_23203.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___219_23203.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___219_23203.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___219_23203.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___219_23203.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___219_23203.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___219_23203.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___219_23203.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___219_23203.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___219_23203.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___219_23203.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___219_23203.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___219_23203.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___219_23203.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___219_23203.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___219_23203.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___219_23203.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___219_23203.FStar_TypeChecker_Env.dsenv)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____23206 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___220_23214 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___220_23214.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___220_23214.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___220_23214.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___220_23214.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___220_23214.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___220_23214.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___220_23214.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___220_23214.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___220_23214.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___220_23214.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___220_23214.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___220_23214.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___220_23214.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___220_23214.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___220_23214.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___220_23214.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___220_23214.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___220_23214.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___220_23214.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___220_23214.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___220_23214.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___220_23214.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___220_23214.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___220_23214.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___220_23214.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___220_23214.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___220_23214.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___220_23214.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___220_23214.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___220_23214.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___220_23214.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___220_23214.FStar_TypeChecker_Env.dsenv)
                                     }) tm1 in
                                match uu____23206 with
                                | (uu____23215,uu____23216,g1) -> g1
                              else
                                (let uu____23219 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___221_23227 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___221_23227.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___221_23227.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___221_23227.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___221_23227.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___221_23227.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___221_23227.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___221_23227.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___221_23227.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___221_23227.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___221_23227.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___221_23227.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___221_23227.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___221_23227.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___221_23227.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___221_23227.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___221_23227.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___221_23227.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___221_23227.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___221_23227.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___221_23227.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___221_23227.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___221_23227.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___221_23227.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___221_23227.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___221_23227.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___221_23227.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___221_23227.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___221_23227.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___221_23227.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___221_23227.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___221_23227.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___221_23227.FStar_TypeChecker_Env.dsenv)
                                      }) tm1 in
                                 match uu____23219 with
                                 | (uu____23228,uu____23229,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___222_23232 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___222_23232.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___222_23232.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___222_23232.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23235 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23241  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23235 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___223_23269 = g in
        let uu____23270 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___223_23269.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___223_23269.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___223_23269.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23270
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
        let uu____23328 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23328 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23341 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23341
      | (reason,uu____23343,uu____23344,e,t,r)::uu____23348 ->
          let uu____23375 =
            let uu____23376 =
              let uu____23381 =
                let uu____23382 = FStar_Syntax_Print.term_to_string t in
                let uu____23383 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23382 uu____23383 in
              (uu____23381, r) in
            FStar_Errors.Error uu____23376 in
          FStar_Exn.raise uu____23375
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___224_23392 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___224_23392.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___224_23392.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___224_23392.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23421 = try_teq false env t1 t2 in
        match uu____23421 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23425 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23425 with
             | FStar_Pervasives_Native.Some uu____23430 -> true
             | FStar_Pervasives_Native.None  -> false)