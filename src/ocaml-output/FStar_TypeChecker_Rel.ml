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
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
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
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
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
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
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
let base_and_refinement:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
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
              (let uu____2119 =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               match uu____2119 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                     (x1,phi1);
                   FStar_Syntax_Syntax.pos = uu____2136;
                   FStar_Syntax_Syntax.vars = uu____2137;_} ->
                   ((x1.FStar_Syntax_Syntax.sort),
                     (FStar_Pervasives_Native.Some (x1, phi1)))
               | tt ->
                   let uu____2163 =
                     let uu____2164 = FStar_Syntax_Print.term_to_string tt in
                     let uu____2165 = FStar_Syntax_Print.tag_of_term tt in
                     FStar_Util.format2 "impossible: Got %s ... %s\n"
                       uu____2164 uu____2165 in
                   failwith uu____2163)
        | FStar_Syntax_Syntax.Tm_uinst uu____2180 ->
            if norm1
            then (t12, FStar_Pervasives_Native.None)
            else
              (let t1' =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               let uu____2217 =
                 let uu____2218 = FStar_Syntax_Subst.compress t1' in
                 uu____2218.FStar_Syntax_Syntax.n in
               match uu____2217 with
               | FStar_Syntax_Syntax.Tm_refine uu____2235 -> aux true t1'
               | uu____2242 -> (t12, FStar_Pervasives_Native.None))
        | FStar_Syntax_Syntax.Tm_fvar uu____2257 ->
            if norm1
            then (t12, FStar_Pervasives_Native.None)
            else
              (let t1' =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               let uu____2288 =
                 let uu____2289 = FStar_Syntax_Subst.compress t1' in
                 uu____2289.FStar_Syntax_Syntax.n in
               match uu____2288 with
               | FStar_Syntax_Syntax.Tm_refine uu____2306 -> aux true t1'
               | uu____2313 -> (t12, FStar_Pervasives_Native.None))
        | FStar_Syntax_Syntax.Tm_app uu____2328 ->
            if norm1
            then (t12, FStar_Pervasives_Native.None)
            else
              (let t1' =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               let uu____2373 =
                 let uu____2374 = FStar_Syntax_Subst.compress t1' in
                 uu____2374.FStar_Syntax_Syntax.n in
               match uu____2373 with
               | FStar_Syntax_Syntax.Tm_refine uu____2391 -> aux true t1'
               | uu____2398 -> (t12, FStar_Pervasives_Native.None))
        | FStar_Syntax_Syntax.Tm_type uu____2413 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_constant uu____2428 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_name uu____2443 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_bvar uu____2458 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_arrow uu____2473 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_abs uu____2500 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_uvar uu____2531 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_let uu____2562 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_match uu____2589 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_meta uu____2626 ->
            let uu____2633 =
              let uu____2634 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2635 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2634 uu____2635 in
            failwith uu____2633
        | FStar_Syntax_Syntax.Tm_ascribed uu____2650 ->
            let uu____2677 =
              let uu____2678 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2679 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2678 uu____2679 in
            failwith uu____2677
        | FStar_Syntax_Syntax.Tm_delayed uu____2694 ->
            let uu____2719 =
              let uu____2720 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2721 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2720 uu____2721 in
            failwith uu____2719
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2736 =
              let uu____2737 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2738 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2737 uu____2738 in
            failwith uu____2736 in
      let uu____2753 = whnf env t1 in aux false uu____2753
let normalize_refinement:
  'Auu____2764 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2764 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun t  ->
      let uu____2789 = base_and_refinement env t in
      FStar_All.pipe_right uu____2789 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2824 = FStar_Syntax_Syntax.null_bv t in
    (uu____2824, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2833 .
    FStar_TypeChecker_Env.env ->
      'Auu____2833 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2850 = base_and_refinement env t in
        match uu____2850 with
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
  fun uu____2908  ->
    match uu____2908 with
    | (t_base,refopt) ->
        let uu____2935 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2935 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2970 =
      let uu____2973 =
        let uu____2976 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2999  ->
                  match uu____2999 with | (uu____3006,uu____3007,x) -> x)) in
        FStar_List.append wl.attempting uu____2976 in
      FStar_List.map (wl_prob_to_string wl) uu____2973 in
    FStar_All.pipe_right uu____2970 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3023 =
          let uu____3036 =
            let uu____3037 = FStar_Syntax_Subst.compress k in
            uu____3037.FStar_Syntax_Syntax.n in
          match uu____3036 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3090 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3090)
              else
                (let uu____3104 = FStar_Syntax_Util.abs_formals t in
                 match uu____3104 with
                 | (ys',t1,uu____3127) ->
                     let uu____3132 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3132))
          | uu____3173 ->
              let uu____3174 =
                let uu____3185 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3185) in
              ((ys, t), uu____3174) in
        match uu____3023 with
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
                 let uu____3234 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3234 c in
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
            let uu____3267 = p_guard prob in
            match uu____3267 with
            | (uu____3272,uv) ->
                ((let uu____3275 =
                    let uu____3276 = FStar_Syntax_Subst.compress uv in
                    uu____3276.FStar_Syntax_Syntax.n in
                  match uu____3275 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3308 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3308
                        then
                          let uu____3309 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3310 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3311 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3309
                            uu____3310 uu____3311
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3313 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___176_3316 = wl in
                  {
                    attempting = (uu___176_3316.attempting);
                    wl_deferred = (uu___176_3316.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___176_3316.defer_ok);
                    smt_ok = (uu___176_3316.smt_ok);
                    tcenv = (uu___176_3316.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3334 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3334
         then
           let uu____3335 = FStar_Util.string_of_int pid in
           let uu____3336 =
             let uu____3337 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3337 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3335 uu____3336
         else ());
        commit sol;
        (let uu___177_3344 = wl in
         {
           attempting = (uu___177_3344.attempting);
           wl_deferred = (uu___177_3344.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___177_3344.defer_ok);
           smt_ok = (uu___177_3344.smt_ok);
           tcenv = (uu___177_3344.tcenv)
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
            | (uu____3386,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3398 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3398 in
          (let uu____3404 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3404
           then
             let uu____3405 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3406 =
               let uu____3407 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3407 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3405 uu____3406
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
        let uu____3442 =
          let uu____3449 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3449 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3442
          (FStar_Util.for_some
             (fun uu____3485  ->
                match uu____3485 with
                | (uv,uu____3491) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3504 'Auu____3505 .
    'Auu____3505 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3504)
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
            let uu____3537 = occurs wl uk t in Prims.op_Negation uu____3537 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3544 =
                 let uu____3545 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3546 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3545 uu____3546 in
               FStar_Pervasives_Native.Some uu____3544) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3563 'Auu____3564 .
    'Auu____3564 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3563)
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
            let uu____3618 = occurs_check env wl uk t in
            match uu____3618 with
            | (occurs_ok,msg) ->
                let uu____3649 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3649, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3676 'Auu____3677 .
    (FStar_Syntax_Syntax.bv,'Auu____3677) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3676) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3676) FStar_Pervasives_Native.tuple2
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
      let uu____3761 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3815  ->
                fun uu____3816  ->
                  match (uu____3815, uu____3816) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3897 =
                        let uu____3898 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3898 in
                      if uu____3897
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3923 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3923
                         then
                           let uu____3936 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3936)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3761 with | (isect,uu____3977) -> FStar_List.rev isect
let binders_eq:
  'Auu____4006 'Auu____4007 .
    (FStar_Syntax_Syntax.bv,'Auu____4007) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4006) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4062  ->
              fun uu____4063  ->
                match (uu____4062, uu____4063) with
                | ((a,uu____4081),(b,uu____4083)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____4102 'Auu____4103 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4103) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4102)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4102)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4154 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4168  ->
                      match uu____4168 with
                      | (b,uu____4174) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4154
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4190 -> FStar_Pervasives_Native.None
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
            let uu____4265 = pat_var_opt env seen hd1 in
            (match uu____4265 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4279 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4279
                   then
                     let uu____4280 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4280
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4299 =
      let uu____4300 = FStar_Syntax_Subst.compress t in
      uu____4300.FStar_Syntax_Syntax.n in
    match uu____4299 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4303 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4320;
           FStar_Syntax_Syntax.pos = uu____4321;
           FStar_Syntax_Syntax.vars = uu____4322;_},uu____4323)
        -> true
    | uu____4360 -> false
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
           FStar_Syntax_Syntax.pos = uu____4485;
           FStar_Syntax_Syntax.vars = uu____4486;_},args)
        -> (t, uv, k, args)
    | uu____4554 -> failwith "Not a flex-uvar"
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
      let uu____4633 = destruct_flex_t t in
      match uu____4633 with
      | (t1,uv,k,args) ->
          let uu____4748 = pat_vars env [] args in
          (match uu____4748 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4846 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4928 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4965 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4970 -> false
let head_match: match_result -> match_result =
  fun uu___153_4974  ->
    match uu___153_4974 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4989 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5000 ->
          let uu____5001 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5001 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5012 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5033 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5042 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5069 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5070 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5071 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5088 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5101 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5125) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5131,uu____5132) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5174) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5195;
             FStar_Syntax_Syntax.index = uu____5196;
             FStar_Syntax_Syntax.sort = t2;_},uu____5198)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5205 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5206 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5207 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5220 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5238 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5238
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
            let uu____5262 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5262
            then FullMatch
            else
              (let uu____5264 =
                 let uu____5273 =
                   let uu____5276 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5276 in
                 let uu____5277 =
                   let uu____5280 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5280 in
                 (uu____5273, uu____5277) in
               MisMatch uu____5264)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5286),FStar_Syntax_Syntax.Tm_uinst (g,uu____5288)) ->
            let uu____5297 = head_matches env f g in
            FStar_All.pipe_right uu____5297 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5306),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5308)) ->
            let uu____5357 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5357
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5364),FStar_Syntax_Syntax.Tm_refine (y,uu____5366)) ->
            let uu____5375 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5375 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5377),uu____5378) ->
            let uu____5383 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5383 head_match
        | (uu____5384,FStar_Syntax_Syntax.Tm_refine (x,uu____5386)) ->
            let uu____5391 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5391 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5392,FStar_Syntax_Syntax.Tm_type
           uu____5393) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5394,FStar_Syntax_Syntax.Tm_arrow uu____5395) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5421),FStar_Syntax_Syntax.Tm_app (head',uu____5423))
            ->
            let uu____5464 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5464 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5466),uu____5467) ->
            let uu____5488 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5488 head_match
        | (uu____5489,FStar_Syntax_Syntax.Tm_app (head1,uu____5491)) ->
            let uu____5512 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5512 head_match
        | uu____5513 ->
            let uu____5518 =
              let uu____5527 = delta_depth_of_term env t11 in
              let uu____5530 = delta_depth_of_term env t21 in
              (uu____5527, uu____5530) in
            MisMatch uu____5518
let head_matches_delta:
  'Auu____5547 .
    FStar_TypeChecker_Env.env ->
      'Auu____5547 ->
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
            let uu____5580 = FStar_Syntax_Util.head_and_args t in
            match uu____5580 with
            | (head1,uu____5598) ->
                let uu____5619 =
                  let uu____5620 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5620.FStar_Syntax_Syntax.n in
                (match uu____5619 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5626 =
                       let uu____5627 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5627 FStar_Option.isSome in
                     if uu____5626
                     then
                       let uu____5646 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5646
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5650 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5753)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5771 =
                     let uu____5780 = maybe_inline t11 in
                     let uu____5783 = maybe_inline t21 in
                     (uu____5780, uu____5783) in
                   match uu____5771 with
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
                (uu____5820,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5838 =
                     let uu____5847 = maybe_inline t11 in
                     let uu____5850 = maybe_inline t21 in
                     (uu____5847, uu____5850) in
                   match uu____5838 with
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
                let uu____5893 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5893 with
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
                let uu____5916 =
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
                (match uu____5916 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5940 -> fail r
            | uu____5949 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5983 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6021 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___154_6035  ->
    match uu___154_6035 with
    | T (t,uu____6037) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6055 = FStar_Syntax_Util.type_u () in
      match uu____6055 with
      | (t,uu____6061) ->
          let uu____6062 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6062
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6075 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6075 FStar_Pervasives_Native.fst
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
        let uu____6141 = head_matches env t1 t' in
        match uu____6141 with
        | MisMatch uu____6142 -> false
        | uu____6151 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6247,imp),T (t2,uu____6250)) -> (t2, imp)
                     | uu____6269 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6336  ->
                    match uu____6336 with
                    | (t2,uu____6350) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6393 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6393 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6468))::tcs2) ->
                       aux
                         (((let uu___178_6503 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_6503.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_6503.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6521 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___155_6574 =
                 match uu___155_6574 with
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
               let uu____6691 = decompose1 [] bs1 in
               (rebuild, matches, uu____6691))
      | uu____6740 ->
          let rebuild uu___156_6746 =
            match uu___156_6746 with
            | [] -> t1
            | uu____6749 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___157_6781  ->
    match uu___157_6781 with
    | T (t,uu____6783) -> t
    | uu____6792 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___158_6796  ->
    match uu___158_6796 with
    | T (t,uu____6798) -> FStar_Syntax_Syntax.as_arg t
    | uu____6807 -> failwith "Impossible"
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
              | (uu____6918,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6943 = new_uvar r scope1 k in
                  (match uu____6943 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6961 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6978 =
                         let uu____6979 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6979 in
                       ((T (gi_xs, mk_kind)), uu____6978))
              | (uu____6992,uu____6993,C uu____6994) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7141 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7158;
                         FStar_Syntax_Syntax.vars = uu____7159;_})
                        ->
                        let uu____7182 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7182 with
                         | (T (gi_xs,uu____7206),prob) ->
                             let uu____7216 =
                               let uu____7217 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7217 in
                             (uu____7216, [prob])
                         | uu____7220 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7235;
                         FStar_Syntax_Syntax.vars = uu____7236;_})
                        ->
                        let uu____7259 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7259 with
                         | (T (gi_xs,uu____7283),prob) ->
                             let uu____7293 =
                               let uu____7294 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7294 in
                             (uu____7293, [prob])
                         | uu____7297 -> failwith "impossible")
                    | (uu____7308,uu____7309,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7311;
                         FStar_Syntax_Syntax.vars = uu____7312;_})
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
                        let uu____7443 =
                          let uu____7452 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7452 FStar_List.unzip in
                        (match uu____7443 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7506 =
                                 let uu____7507 =
                                   let uu____7510 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7510 un_T in
                                 let uu____7511 =
                                   let uu____7520 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7520
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7507;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7511;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7506 in
                             ((C gi_xs), sub_probs))
                    | uu____7529 ->
                        let uu____7542 = sub_prob scope1 args q in
                        (match uu____7542 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7141 with
                   | (tc,probs) ->
                       let uu____7573 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7636,uu____7637),T
                            (t,uu____7639)) ->
                             let b1 =
                               ((let uu___179_7676 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___179_7676.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___179_7676.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7677 =
                               let uu____7684 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7684 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7677)
                         | uu____7719 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7573 with
                        | (bopt,scope2,args1) ->
                            let uu____7803 = aux scope2 args1 qs2 in
                            (match uu____7803 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7840 =
                                         let uu____7843 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7843 in
                                       FStar_Syntax_Util.mk_conj_l uu____7840
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7866 =
                                         let uu____7869 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7870 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7869 :: uu____7870 in
                                       FStar_Syntax_Util.mk_conj_l uu____7866 in
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
  'Auu____7941 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7941)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7941)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___180_7962 = p in
      let uu____7967 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7968 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___180_7962.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7967;
        FStar_TypeChecker_Common.relation =
          (uu___180_7962.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7968;
        FStar_TypeChecker_Common.element =
          (uu___180_7962.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___180_7962.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___180_7962.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___180_7962.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___180_7962.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___180_7962.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7982 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7982
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7991 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8013 = compress_prob wl pr in
        FStar_All.pipe_right uu____8013 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8023 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8023 with
           | (lh,uu____8043) ->
               let uu____8064 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8064 with
                | (rh,uu____8084) ->
                    let uu____8105 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8122,FStar_Syntax_Syntax.Tm_uvar uu____8123)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8160,uu____8161)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8182,FStar_Syntax_Syntax.Tm_uvar uu____8183)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8204,uu____8205)
                          ->
                          let uu____8222 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8222 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8271 ->
                                    let rank =
                                      let uu____8279 = is_top_level_prob prob in
                                      if uu____8279
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8281 =
                                      let uu___181_8286 = tp in
                                      let uu____8291 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___181_8286.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___181_8286.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___181_8286.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8291;
                                        FStar_TypeChecker_Common.element =
                                          (uu___181_8286.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___181_8286.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___181_8286.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___181_8286.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___181_8286.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___181_8286.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8281)))
                      | (uu____8302,FStar_Syntax_Syntax.Tm_uvar uu____8303)
                          ->
                          let uu____8320 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8320 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8369 ->
                                    let uu____8376 =
                                      let uu___182_8383 = tp in
                                      let uu____8388 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___182_8383.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8388;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___182_8383.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___182_8383.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___182_8383.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___182_8383.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___182_8383.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___182_8383.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___182_8383.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___182_8383.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8376)))
                      | (uu____8405,uu____8406) -> (rigid_rigid, tp) in
                    (match uu____8105 with
                     | (rank,tp1) ->
                         let uu____8425 =
                           FStar_All.pipe_right
                             (let uu___183_8431 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___183_8431.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___183_8431.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___183_8431.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___183_8431.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___183_8431.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___183_8431.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___183_8431.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___183_8431.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___183_8431.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8425))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8441 =
            FStar_All.pipe_right
              (let uu___184_8447 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___184_8447.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___184_8447.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___184_8447.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___184_8447.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___184_8447.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___184_8447.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___184_8447.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___184_8447.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___184_8447.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8441)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8503 probs =
      match uu____8503 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8556 = rank wl hd1 in
               (match uu____8556 with
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
    match projectee with | UDeferred _0 -> true | uu____8666 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8680 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8694 -> false
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
                        let uu____8739 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8739 with
                        | (k,uu____8745) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8755 -> false)))
            | uu____8756 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8807 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8807 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8810 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8820 =
                     let uu____8821 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8822 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8821
                       uu____8822 in
                   UFailed uu____8820)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8842 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8842 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8864 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8864 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8867 ->
                let uu____8872 =
                  let uu____8873 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8874 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8873
                    uu____8874 msg in
                UFailed uu____8872 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8875,uu____8876) ->
              let uu____8877 =
                let uu____8878 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8879 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8878 uu____8879 in
              failwith uu____8877
          | (FStar_Syntax_Syntax.U_unknown ,uu____8880) ->
              let uu____8881 =
                let uu____8882 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8883 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8882 uu____8883 in
              failwith uu____8881
          | (uu____8884,FStar_Syntax_Syntax.U_bvar uu____8885) ->
              let uu____8886 =
                let uu____8887 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8888 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8887 uu____8888 in
              failwith uu____8886
          | (uu____8889,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8890 =
                let uu____8891 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8892 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8891 uu____8892 in
              failwith uu____8890
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8916 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8916
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8938 = occurs_univ v1 u3 in
              if uu____8938
              then
                let uu____8939 =
                  let uu____8940 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8941 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8940 uu____8941 in
                try_umax_components u11 u21 uu____8939
              else
                (let uu____8943 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8943)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8963 = occurs_univ v1 u3 in
              if uu____8963
              then
                let uu____8964 =
                  let uu____8965 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8966 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8965 uu____8966 in
                try_umax_components u11 u21 uu____8964
              else
                (let uu____8968 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8968)
          | (FStar_Syntax_Syntax.U_max uu____8977,uu____8978) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8984 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8984
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8986,FStar_Syntax_Syntax.U_max uu____8987) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8993 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8993
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8995,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8996,FStar_Syntax_Syntax.U_name
             uu____8997) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8998) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8999) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9000,FStar_Syntax_Syntax.U_succ
             uu____9001) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9002,FStar_Syntax_Syntax.U_zero
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
      let uu____9096 = bc1 in
      match uu____9096 with
      | (bs1,mk_cod1) ->
          let uu____9137 = bc2 in
          (match uu____9137 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9207 = FStar_Util.first_N n1 bs in
                 match uu____9207 with
                 | (bs3,rest) ->
                     let uu____9232 = mk_cod rest in (bs3, uu____9232) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9261 =
                   let uu____9268 = mk_cod1 [] in (bs1, uu____9268) in
                 let uu____9271 =
                   let uu____9278 = mk_cod2 [] in (bs2, uu____9278) in
                 (uu____9261, uu____9271)
               else
                 if l1 > l2
                 then
                   (let uu____9320 = curry l2 bs1 mk_cod1 in
                    let uu____9333 =
                      let uu____9340 = mk_cod2 [] in (bs2, uu____9340) in
                    (uu____9320, uu____9333))
                 else
                   (let uu____9356 =
                      let uu____9363 = mk_cod1 [] in (bs1, uu____9363) in
                    let uu____9366 = curry l1 bs2 mk_cod2 in
                    (uu____9356, uu____9366)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9487 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9487
       then
         let uu____9488 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9488
       else ());
      (let uu____9490 = next_prob probs in
       match uu____9490 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___185_9511 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___185_9511.wl_deferred);
               ctr = (uu___185_9511.ctr);
               defer_ok = (uu___185_9511.defer_ok);
               smt_ok = (uu___185_9511.smt_ok);
               tcenv = (uu___185_9511.tcenv)
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
                  let uu____9522 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9522 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9527 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9527 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9532,uu____9533) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9550 ->
                let uu____9559 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9618  ->
                          match uu____9618 with
                          | (c,uu____9626,uu____9627) -> c < probs.ctr)) in
                (match uu____9559 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9668 =
                            FStar_List.map
                              (fun uu____9683  ->
                                 match uu____9683 with
                                 | (uu____9694,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9668
                      | uu____9697 ->
                          let uu____9706 =
                            let uu___186_9707 = probs in
                            let uu____9708 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9729  ->
                                      match uu____9729 with
                                      | (uu____9736,uu____9737,y) -> y)) in
                            {
                              attempting = uu____9708;
                              wl_deferred = rest;
                              ctr = (uu___186_9707.ctr);
                              defer_ok = (uu___186_9707.defer_ok);
                              smt_ok = (uu___186_9707.smt_ok);
                              tcenv = (uu___186_9707.tcenv)
                            } in
                          solve env uu____9706))))
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
            let uu____9744 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9744 with
            | USolved wl1 ->
                let uu____9746 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9746
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
                  let uu____9792 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9792 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9795 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9807;
                  FStar_Syntax_Syntax.vars = uu____9808;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9811;
                  FStar_Syntax_Syntax.vars = uu____9812;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9826,uu____9827) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9834,FStar_Syntax_Syntax.Tm_uinst uu____9835) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9842 -> USolved wl
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
            ((let uu____9852 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9852
              then
                let uu____9853 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9853 msg
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
        (let uu____9862 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9862
         then
           let uu____9863 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9863
         else ());
        (let uu____9865 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9865 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9927 = head_matches_delta env () t1 t2 in
               match uu____9927 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9968 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10017 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10032 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10033 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10032, uu____10033)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10038 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10039 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10038, uu____10039) in
                        (match uu____10017 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10065 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10065 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10096 =
                                    let uu____10105 =
                                      let uu____10108 =
                                        let uu____10111 =
                                          let uu____10112 =
                                            let uu____10119 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10119) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10112 in
                                        FStar_Syntax_Syntax.mk uu____10111 in
                                      uu____10108
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10127 =
                                      let uu____10130 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10130] in
                                    (uu____10105, uu____10127) in
                                  FStar_Pervasives_Native.Some uu____10096
                              | (uu____10143,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10145)) ->
                                  let uu____10150 =
                                    let uu____10157 =
                                      let uu____10160 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10160] in
                                    (t11, uu____10157) in
                                  FStar_Pervasives_Native.Some uu____10150
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10170),uu____10171) ->
                                  let uu____10176 =
                                    let uu____10183 =
                                      let uu____10186 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10186] in
                                    (t21, uu____10183) in
                                  FStar_Pervasives_Native.Some uu____10176
                              | uu____10195 ->
                                  let uu____10200 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10200 with
                                   | (head1,uu____10224) ->
                                       let uu____10245 =
                                         let uu____10246 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10246.FStar_Syntax_Syntax.n in
                                       (match uu____10245 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10257;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10259;_}
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
                                        | uu____10266 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10279) ->
                  let uu____10304 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___159_10330  ->
                            match uu___159_10330 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10337 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10337 with
                                      | (u',uu____10353) ->
                                          let uu____10374 =
                                            let uu____10375 = whnf env u' in
                                            uu____10375.FStar_Syntax_Syntax.n in
                                          (match uu____10374 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10379) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10404 -> false))
                                 | uu____10405 -> false)
                            | uu____10408 -> false)) in
                  (match uu____10304 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10442 tps =
                         match uu____10442 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10490 =
                                    let uu____10499 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10499 in
                                  (match uu____10490 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10534 -> FStar_Pervasives_Native.None) in
                       let uu____10543 =
                         let uu____10552 =
                           let uu____10559 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10559, []) in
                         make_lower_bound uu____10552 lower_bounds in
                       (match uu____10543 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10571 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10571
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
                            ((let uu____10591 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10591
                              then
                                let wl' =
                                  let uu___187_10593 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___187_10593.wl_deferred);
                                    ctr = (uu___187_10593.ctr);
                                    defer_ok = (uu___187_10593.defer_ok);
                                    smt_ok = (uu___187_10593.smt_ok);
                                    tcenv = (uu___187_10593.tcenv)
                                  } in
                                let uu____10594 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10594
                              else ());
                             (let uu____10596 =
                                solve_t env eq_prob
                                  (let uu___188_10598 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___188_10598.wl_deferred);
                                     ctr = (uu___188_10598.ctr);
                                     defer_ok = (uu___188_10598.defer_ok);
                                     smt_ok = (uu___188_10598.smt_ok);
                                     tcenv = (uu___188_10598.tcenv)
                                   }) in
                              match uu____10596 with
                              | Success uu____10601 ->
                                  let wl1 =
                                    let uu___189_10603 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___189_10603.wl_deferred);
                                      ctr = (uu___189_10603.ctr);
                                      defer_ok = (uu___189_10603.defer_ok);
                                      smt_ok = (uu___189_10603.smt_ok);
                                      tcenv = (uu___189_10603.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10605 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10610 -> FStar_Pervasives_Native.None))))
              | uu____10611 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10620 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10620
         then
           let uu____10621 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10621
         else ());
        (let uu____10623 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10623 with
         | (u,args) ->
             let uu____10662 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10662 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10703 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10703 with
                    | (h1,args1) ->
                        let uu____10744 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10744 with
                         | (h2,uu____10764) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10791 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10791
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10809 =
                                          let uu____10812 =
                                            let uu____10813 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10813 in
                                          [uu____10812] in
                                        FStar_Pervasives_Native.Some
                                          uu____10809))
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
                                       (let uu____10846 =
                                          let uu____10849 =
                                            let uu____10850 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10850 in
                                          [uu____10849] in
                                        FStar_Pervasives_Native.Some
                                          uu____10846))
                                  else FStar_Pervasives_Native.None
                              | uu____10864 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10954 =
                               let uu____10963 =
                                 let uu____10966 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10966 in
                               (uu____10963, m1) in
                             FStar_Pervasives_Native.Some uu____10954)
                    | (uu____10979,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10981)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11029),uu____11030) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11077 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11130) ->
                       let uu____11155 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___160_11181  ->
                                 match uu___160_11181 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11188 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11188 with
                                           | (u',uu____11204) ->
                                               let uu____11225 =
                                                 let uu____11226 =
                                                   whnf env u' in
                                                 uu____11226.FStar_Syntax_Syntax.n in
                                               (match uu____11225 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11230) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11255 -> false))
                                      | uu____11256 -> false)
                                 | uu____11259 -> false)) in
                       (match uu____11155 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11297 tps =
                              match uu____11297 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11359 =
                                         let uu____11370 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11370 in
                                       (match uu____11359 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11421 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11432 =
                              let uu____11443 =
                                let uu____11452 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11452, []) in
                              make_upper_bound uu____11443 upper_bounds in
                            (match uu____11432 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11466 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11466
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
                                 ((let uu____11492 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11492
                                   then
                                     let wl' =
                                       let uu___190_11494 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___190_11494.wl_deferred);
                                         ctr = (uu___190_11494.ctr);
                                         defer_ok = (uu___190_11494.defer_ok);
                                         smt_ok = (uu___190_11494.smt_ok);
                                         tcenv = (uu___190_11494.tcenv)
                                       } in
                                     let uu____11495 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11495
                                   else ());
                                  (let uu____11497 =
                                     solve_t env eq_prob
                                       (let uu___191_11499 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___191_11499.wl_deferred);
                                          ctr = (uu___191_11499.ctr);
                                          defer_ok =
                                            (uu___191_11499.defer_ok);
                                          smt_ok = (uu___191_11499.smt_ok);
                                          tcenv = (uu___191_11499.tcenv)
                                        }) in
                                   match uu____11497 with
                                   | Success uu____11502 ->
                                       let wl1 =
                                         let uu___192_11504 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___192_11504.wl_deferred);
                                           ctr = (uu___192_11504.ctr);
                                           defer_ok =
                                             (uu___192_11504.defer_ok);
                                           smt_ok = (uu___192_11504.smt_ok);
                                           tcenv = (uu___192_11504.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11506 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11511 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11512 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11587 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11587
                      then
                        let uu____11588 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11588
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___193_11642 = hd1 in
                      let uu____11643 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___193_11642.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___193_11642.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11643
                      } in
                    let hd21 =
                      let uu___194_11647 = hd2 in
                      let uu____11648 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___194_11647.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___194_11647.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11648
                      } in
                    let prob =
                      let uu____11652 =
                        let uu____11657 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11657 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11652 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11668 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11668 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11672 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11672 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11710 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11715 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11710 uu____11715 in
                         ((let uu____11725 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11725
                           then
                             let uu____11726 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11727 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11726 uu____11727
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11750 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11760 = aux scope env [] bs1 bs2 in
              match uu____11760 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11784 = compress_tprob wl problem in
        solve_t' env uu____11784 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11817 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11817 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11848,uu____11849) ->
                   let rec may_relate head3 =
                     let uu____11874 =
                       let uu____11875 = FStar_Syntax_Subst.compress head3 in
                       uu____11875.FStar_Syntax_Syntax.n in
                     match uu____11874 with
                     | FStar_Syntax_Syntax.Tm_name uu____11878 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11879 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11902;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11903;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11906;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11907;
                           FStar_Syntax_Syntax.fv_qual = uu____11908;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11912,uu____11913) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11955) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11961) ->
                         may_relate t
                     | uu____11966 -> false in
                   let uu____11967 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11967
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
                                let uu____11984 =
                                  let uu____11985 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11985 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11984 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11987 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11987
                   else
                     (let uu____11989 =
                        let uu____11990 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11991 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11990 uu____11991 in
                      giveup env1 uu____11989 orig)
               | (uu____11992,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___195_12006 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___195_12006.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___195_12006.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___195_12006.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___195_12006.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___195_12006.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___195_12006.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___195_12006.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___195_12006.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12007,FStar_Pervasives_Native.None ) ->
                   ((let uu____12019 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12019
                     then
                       let uu____12020 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12021 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12022 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12023 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12020
                         uu____12021 uu____12022 uu____12023
                     else ());
                    (let uu____12025 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12025 with
                     | (head11,args1) ->
                         let uu____12062 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12062 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12116 =
                                  let uu____12117 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12118 = args_to_string args1 in
                                  let uu____12119 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12120 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12117 uu____12118 uu____12119
                                    uu____12120 in
                                giveup env1 uu____12116 orig
                              else
                                (let uu____12122 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12128 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12128 = FStar_Syntax_Util.Equal) in
                                 if uu____12122
                                 then
                                   let uu____12129 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12129 with
                                   | USolved wl2 ->
                                       let uu____12131 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12131
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12135 =
                                      base_and_refinement env1 t1 in
                                    match uu____12135 with
                                    | (base1,refinement1) ->
                                        let uu____12160 =
                                          base_and_refinement env1 t2 in
                                        (match uu____12160 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12217 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12217 with
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
                                                           (fun uu____12239 
                                                              ->
                                                              fun uu____12240
                                                                 ->
                                                                match 
                                                                  (uu____12239,
                                                                    uu____12240)
                                                                with
                                                                | ((a,uu____12258),
                                                                   (a',uu____12260))
                                                                    ->
                                                                    let uu____12269
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
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____12269)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12279 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12279 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12285 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___196_12321 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___196_12321.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12360 =
          match uu____12360 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12576  ->
                              match uu____12576 with
                              | (x,imp) ->
                                  let uu____12587 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12587, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12600 = FStar_Syntax_Util.type_u () in
                      match uu____12600 with
                      | (t1,uu____12606) ->
                          let uu____12607 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12607 in
                    let uu____12612 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12612 with
                     | (t',tm_u1) ->
                         let uu____12625 = destruct_flex_t t' in
                         (match uu____12625 with
                          | (uu____12662,u1,k1,uu____12665) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12724 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12724 in
                              let sol =
                                let uu____12728 =
                                  let uu____12737 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12737) in
                                TERM uu____12728 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____12873 = pat_var_opt env pat_args hd1 in
                    (match uu____12873 with
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
                                    (fun uu____12936  ->
                                       match uu____12936 with
                                       | (x,uu____12942) ->
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
                            let uu____12957 =
                              let uu____12958 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____12958 in
                            if uu____12957
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____12970 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____12970 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____12985::uu____12986) ->
                    let uu____13017 =
                      let uu____13030 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____13030 in
                    (match uu____13017 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____13069 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____13076::uu____13077,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____13112 =
                let uu____13125 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13125 in
              (match uu____13112 with
               | (all_formals,res_t) ->
                   let uu____13150 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13150 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13184 = lhs in
          match uu____13184 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13194 ->
                    let uu____13195 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13195 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13218 = p in
          match uu____13218 with
          | (((u,k),xs,c),ps,(h,uu____13229,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13311 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13311 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13334 = h gs_xs in
                     let uu____13335 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13334 uu____13335 in
                   ((let uu____13341 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13341
                     then
                       let uu____13342 =
                         let uu____13345 =
                           let uu____13346 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13346
                             (FStar_String.concat "\n\t") in
                         let uu____13351 =
                           let uu____13354 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13355 =
                             let uu____13358 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13359 =
                               let uu____13362 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13363 =
                                 let uu____13366 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13367 =
                                   let uu____13370 =
                                     let uu____13371 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13371
                                       (FStar_String.concat ", ") in
                                   let uu____13376 =
                                     let uu____13379 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13379] in
                                   uu____13370 :: uu____13376 in
                                 uu____13366 :: uu____13367 in
                               uu____13362 :: uu____13363 in
                             uu____13358 :: uu____13359 in
                           uu____13354 :: uu____13355 in
                         uu____13345 :: uu____13351 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13342
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___161_13400 =
          match uu___161_13400 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13432 = p in
          match uu____13432 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13523 = FStar_List.nth ps i in
              (match uu____13523 with
               | (pi,uu____13527) ->
                   let uu____13532 = FStar_List.nth xs i in
                   (match uu____13532 with
                    | (xi,uu____13544) ->
                        let rec gs k =
                          let uu____13557 =
                            let uu____13570 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13570 in
                          match uu____13557 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13645)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13658 = new_uvar r xs k_a in
                                    (match uu____13658 with
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
                                         let uu____13680 = aux subst2 tl1 in
                                         (match uu____13680 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13707 =
                                                let uu____13710 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13710 :: gi_xs' in
                                              let uu____13711 =
                                                let uu____13714 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13714 :: gi_ps' in
                                              (uu____13707, uu____13711))) in
                              aux [] bs in
                        let uu____13719 =
                          let uu____13720 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13720 in
                        if uu____13719
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13724 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13724 with
                           | (g_xs,uu____13736) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13747 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13748 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13747
                                   uu____13748 in
                               let sub1 =
                                 let uu____13754 =
                                   let uu____13759 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13762 =
                                     let uu____13765 =
                                       FStar_List.map
                                         (fun uu____13780  ->
                                            match uu____13780 with
                                            | (uu____13789,uu____13790,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13765 in
                                   mk_problem (p_scope orig) orig uu____13759
                                     (p_rel orig) uu____13762
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13754 in
                               ((let uu____13805 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13805
                                 then
                                   let uu____13806 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13807 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13806 uu____13807
                                 else ());
                                (let wl2 =
                                   let uu____13810 =
                                     let uu____13813 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13813 in
                                   solve_prob orig uu____13810
                                     [TERM (u, proj)] wl1 in
                                 let uu____13822 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13822))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13853 = lhs in
          match uu____13853 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13889 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13889 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13922 =
                        let uu____13969 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13969) in
                      FStar_Pervasives_Native.Some uu____13922
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14113 =
                           let uu____14120 =
                             let uu____14121 = FStar_Syntax_Subst.compress k1 in
                             uu____14121.FStar_Syntax_Syntax.n in
                           (uu____14120, args) in
                         match uu____14113 with
                         | (uu____14132,[]) ->
                             let uu____14135 =
                               let uu____14146 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14146) in
                             FStar_Pervasives_Native.Some uu____14135
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14167,uu____14168) ->
                             let uu____14189 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14189 with
                              | (uv1,uv_args) ->
                                  let uu____14232 =
                                    let uu____14233 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14233.FStar_Syntax_Syntax.n in
                                  (match uu____14232 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14243) ->
                                       let uu____14268 =
                                         pat_vars env [] uv_args in
                                       (match uu____14268 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14295  ->
                                                      let uu____14296 =
                                                        let uu____14297 =
                                                          let uu____14298 =
                                                            let uu____14303 =
                                                              let uu____14304
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14304
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14303 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14298 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14297 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14296)) in
                                            let c1 =
                                              let uu____14314 =
                                                let uu____14315 =
                                                  let uu____14320 =
                                                    let uu____14321 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14321
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14320 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14315 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14314 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14334 =
                                                let uu____14337 =
                                                  let uu____14338 =
                                                    let uu____14341 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14341
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14338 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14337 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14334 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14359 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14364,uu____14365) ->
                             let uu____14384 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14384 with
                              | (uv1,uv_args) ->
                                  let uu____14427 =
                                    let uu____14428 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14428.FStar_Syntax_Syntax.n in
                                  (match uu____14427 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14438) ->
                                       let uu____14463 =
                                         pat_vars env [] uv_args in
                                       (match uu____14463 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14490  ->
                                                      let uu____14491 =
                                                        let uu____14492 =
                                                          let uu____14493 =
                                                            let uu____14498 =
                                                              let uu____14499
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14499
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14498 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14493 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14492 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14491)) in
                                            let c1 =
                                              let uu____14509 =
                                                let uu____14510 =
                                                  let uu____14515 =
                                                    let uu____14516 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14516
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14515 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14510 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14509 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14529 =
                                                let uu____14532 =
                                                  let uu____14533 =
                                                    let uu____14536 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14536
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14533 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14532 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14529 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14554 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14561) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14602 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14602
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14638 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14638 with
                                  | (args1,rest) ->
                                      let uu____14667 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14667 with
                                       | (xs2,c2) ->
                                           let uu____14680 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14680
                                             (fun uu____14704  ->
                                                match uu____14704 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14744 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14744 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14812 =
                                        let uu____14817 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14817 in
                                      FStar_All.pipe_right uu____14812
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14832 ->
                             let uu____14839 =
                               let uu____14840 =
                                 let uu____14845 =
                                   let uu____14846 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14847 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14848 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14846 uu____14847 uu____14848 in
                                 (uu____14845, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14840 in
                             FStar_Exn.raise uu____14839 in
                       let uu____14855 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14855
                         (fun uu____14910  ->
                            match uu____14910 with
                            | (xs1,c1) ->
                                let uu____14959 =
                                  let uu____15000 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15000) in
                                FStar_Pervasives_Native.Some uu____14959)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15121 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15137 = project orig env wl1 i st in
                     match uu____15137 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15151) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15166 = imitate orig env wl1 st in
                  match uu____15166 with
                  | Failed uu____15171 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15202 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15202 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15227 =
                      let uu____15228 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15228 wl2 in
                    (match uu____15227 with
                     | Failed uu____15229 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15247 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15247 with
                | (hd1,uu____15263) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15284 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15297 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15298 -> true
                     | uu____15315 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15319 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15319
                         then true
                         else
                           ((let uu____15322 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15322
                             then
                               let uu____15323 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15323
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15343 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15343 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15356 =
                            let uu____15357 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15357 in
                          giveup_or_defer1 orig uu____15356
                        else
                          (let uu____15359 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15359
                           then
                             let uu____15360 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15360
                              then
                                let uu____15361 = subterms args_lhs in
                                imitate' orig env wl1 uu____15361
                              else
                                ((let uu____15366 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15366
                                  then
                                    let uu____15367 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15368 = names_to_string fvs1 in
                                    let uu____15369 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15367 uu____15368 uu____15369
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
                               (let uu____15373 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15373
                                then
                                  ((let uu____15375 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15375
                                    then
                                      let uu____15376 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15377 = names_to_string fvs1 in
                                      let uu____15378 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15376 uu____15377 uu____15378
                                    else ());
                                   (let uu____15380 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15380))
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
                     (let uu____15391 =
                        let uu____15392 = FStar_Syntax_Free.names t1 in
                        check_head uu____15392 t2 in
                      if uu____15391
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15403 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15403
                          then
                            let uu____15404 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15405 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15404 uu____15405
                          else ());
                         (let uu____15413 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15413))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15490 uu____15491 r =
               match (uu____15490, uu____15491) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15689 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15689
                   then
                     let uu____15690 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15690
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15714 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15714
                       then
                         let uu____15715 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15716 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15717 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15718 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15719 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15715 uu____15716 uu____15717 uu____15718
                           uu____15719
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15779 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15779 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15793 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15793 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15847 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15847 in
                                  let uu____15850 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15850 k3)
                           else
                             (let uu____15854 =
                                let uu____15855 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15856 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15857 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15855 uu____15856 uu____15857 in
                              failwith uu____15854) in
                       let uu____15858 =
                         let uu____15865 =
                           let uu____15878 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15878 in
                         match uu____15865 with
                         | (bs,k1') ->
                             let uu____15903 =
                               let uu____15916 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15916 in
                             (match uu____15903 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15944 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15944 in
                                  let uu____15953 =
                                    let uu____15958 =
                                      let uu____15959 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15959.FStar_Syntax_Syntax.n in
                                    let uu____15962 =
                                      let uu____15963 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15963.FStar_Syntax_Syntax.n in
                                    (uu____15958, uu____15962) in
                                  (match uu____15953 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15972,uu____15973) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____15976,FStar_Syntax_Syntax.Tm_type
                                      uu____15977) -> (k2'_ys, [sub_prob])
                                   | uu____15980 ->
                                       let uu____15985 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15985 with
                                        | (t,uu____15997) ->
                                            let uu____15998 = new_uvar r zs t in
                                            (match uu____15998 with
                                             | (k_zs,uu____16010) ->
                                                 let kprob =
                                                   let uu____16012 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____16012 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15858 with
                       | (k_u',sub_probs) ->
                           let uu____16029 =
                             let uu____16040 =
                               let uu____16041 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16041 in
                             let uu____16050 =
                               let uu____16053 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16053 in
                             let uu____16056 =
                               let uu____16059 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16059 in
                             (uu____16040, uu____16050, uu____16056) in
                           (match uu____16029 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16078 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16078 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16097 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16097
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16101 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16101 with
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
             let solve_one_pat uu____16154 uu____16155 =
               match (uu____16154, uu____16155) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16273 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16273
                     then
                       let uu____16274 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16275 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16274 uu____16275
                     else ());
                    (let uu____16277 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16277
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16296  ->
                              fun uu____16297  ->
                                match (uu____16296, uu____16297) with
                                | ((a,uu____16315),(t21,uu____16317)) ->
                                    let uu____16326 =
                                      let uu____16331 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16331
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16326
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16337 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16337 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16352 = occurs_check env wl (u1, k1) t21 in
                        match uu____16352 with
                        | (occurs_ok,uu____16360) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16368 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16368
                            then
                              let sol =
                                let uu____16370 =
                                  let uu____16379 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16379) in
                                TERM uu____16370 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16386 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16386
                               then
                                 let uu____16387 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16387 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16411,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16437 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16437
                                       then
                                         let uu____16438 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16438
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16445 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16447 = lhs in
             match uu____16447 with
             | (t1,u1,k1,args1) ->
                 let uu____16452 = rhs in
                 (match uu____16452 with
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
                       | uu____16492 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16502 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16502 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16520) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16527 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16527
                                    then
                                      let uu____16528 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16528
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16535 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16537 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16537
        then
          let uu____16538 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16538
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16542 = FStar_Util.physical_equality t1 t2 in
           if uu____16542
           then
             let uu____16543 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16543
           else
             ((let uu____16546 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16546
               then
                 let uu____16547 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16547
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16550,uu____16551) ->
                   let uu____16578 =
                     let uu___197_16579 = problem in
                     let uu____16580 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16579.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16580;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16579.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16579.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16579.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16579.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16579.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16579.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16579.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16579.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16578 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16581,uu____16582) ->
                   let uu____16589 =
                     let uu___197_16590 = problem in
                     let uu____16591 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16590.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16591;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_16590.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16590.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16590.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16590.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___197_16590.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16590.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16590.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16590.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16589 wl
               | (uu____16592,FStar_Syntax_Syntax.Tm_ascribed uu____16593) ->
                   let uu____16620 =
                     let uu___198_16621 = problem in
                     let uu____16622 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16621.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16621.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16621.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16622;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16621.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16621.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16621.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16621.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16621.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16621.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16620 wl
               | (uu____16623,FStar_Syntax_Syntax.Tm_meta uu____16624) ->
                   let uu____16631 =
                     let uu___198_16632 = problem in
                     let uu____16633 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16632.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16632.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_16632.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16633;
                       FStar_TypeChecker_Common.element =
                         (uu___198_16632.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16632.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___198_16632.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16632.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16632.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16632.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16631 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16634,uu____16635) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16636,FStar_Syntax_Syntax.Tm_bvar uu____16637) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___162_16692 =
                     match uu___162_16692 with
                     | [] -> c
                     | bs ->
                         let uu____16714 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16714 in
                   let uu____16723 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16723 with
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
                                   let uu____16865 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16865
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16867 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16867))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___163_16943 =
                     match uu___163_16943 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16977 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16977 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17113 =
                                   let uu____17118 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17119 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17118
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17119 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____17113))
               | (FStar_Syntax_Syntax.Tm_abs uu____17124,uu____17125) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17150 -> true
                     | uu____17167 -> false in
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
                       (let uu____17214 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17222 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17222.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17222.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17222.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17222.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17222.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17222.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17222.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17222.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17222.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17222.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17222.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17222.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17222.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17222.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17222.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17222.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17222.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17222.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17222.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17222.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17222.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17222.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17222.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17222.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17222.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17222.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17222.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17222.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17222.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17222.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17214 with
                        | (uu____17225,ty,uu____17227) ->
                            let uu____17228 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17228) in
                   let uu____17229 =
                     let uu____17246 = maybe_eta t1 in
                     let uu____17253 = maybe_eta t2 in
                     (uu____17246, uu____17253) in
                   (match uu____17229 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17295 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17295.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17295.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17295.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17295.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17295.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17295.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17295.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17295.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17318 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17318
                        then
                          let uu____17319 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17319 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17334 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17334.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17334.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17334.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17334.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17334.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17334.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17334.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17334.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17358 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17358
                        then
                          let uu____17359 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17359 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17374 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17374.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17374.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17374.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17374.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17374.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17374.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17374.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17374.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17378 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17395,FStar_Syntax_Syntax.Tm_abs uu____17396) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17421 -> true
                     | uu____17438 -> false in
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
                       (let uu____17485 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___199_17493 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___199_17493.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___199_17493.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___199_17493.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___199_17493.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___199_17493.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___199_17493.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___199_17493.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___199_17493.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___199_17493.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___199_17493.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___199_17493.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___199_17493.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___199_17493.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___199_17493.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___199_17493.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___199_17493.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___199_17493.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___199_17493.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___199_17493.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___199_17493.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___199_17493.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___199_17493.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___199_17493.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___199_17493.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___199_17493.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___199_17493.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___199_17493.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___199_17493.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___199_17493.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___199_17493.FStar_TypeChecker_Env.dsenv)
                             }) t in
                        match uu____17485 with
                        | (uu____17496,ty,uu____17498) ->
                            let uu____17499 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17499) in
                   let uu____17500 =
                     let uu____17517 = maybe_eta t1 in
                     let uu____17524 = maybe_eta t2 in
                     (uu____17517, uu____17524) in
                   (match uu____17500 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___200_17566 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___200_17566.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___200_17566.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___200_17566.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___200_17566.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___200_17566.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___200_17566.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___200_17566.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___200_17566.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17589 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17589
                        then
                          let uu____17590 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17590 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17605 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17605.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17605.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17605.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17605.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17605.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17605.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17605.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17605.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17629 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17629
                        then
                          let uu____17630 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17630 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___201_17645 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___201_17645.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___201_17645.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___201_17645.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___201_17645.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___201_17645.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___201_17645.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___201_17645.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___201_17645.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17649 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17666,FStar_Syntax_Syntax.Tm_refine uu____17667) ->
                   let uu____17680 = as_refinement env wl t1 in
                   (match uu____17680 with
                    | (x1,phi1) ->
                        let uu____17687 = as_refinement env wl t2 in
                        (match uu____17687 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17695 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17695 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17733 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17733
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17737 =
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
                                 let uu____17743 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17743 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17752 =
                                   let uu____17757 =
                                     let uu____17758 =
                                       let uu____17765 =
                                         FStar_Syntax_Syntax.mk_binder x11 in
                                       [uu____17765] in
                                     FStar_List.append (p_scope orig)
                                       uu____17758 in
                                   mk_problem uu____17757 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17752 in
                               let uu____17774 =
                                 solve env1
                                   (let uu___202_17776 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___202_17776.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___202_17776.smt_ok);
                                      tcenv = (uu___202_17776.tcenv)
                                    }) in
                               (match uu____17774 with
                                | Failed uu____17783 -> fallback ()
                                | Success uu____17788 ->
                                    let guard =
                                      let uu____17792 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17797 =
                                        let uu____17798 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17798
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17792
                                        uu____17797 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___203_17807 = wl1 in
                                      {
                                        attempting =
                                          (uu___203_17807.attempting);
                                        wl_deferred =
                                          (uu___203_17807.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___203_17807.defer_ok);
                                        smt_ok = (uu___203_17807.smt_ok);
                                        tcenv = (uu___203_17807.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17809,FStar_Syntax_Syntax.Tm_uvar uu____17810) ->
                   let uu____17843 = destruct_flex_t t1 in
                   let uu____17844 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17843 uu____17844
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17845;
                     FStar_Syntax_Syntax.pos = uu____17846;
                     FStar_Syntax_Syntax.vars = uu____17847;_},uu____17848),FStar_Syntax_Syntax.Tm_uvar
                  uu____17849) ->
                   let uu____17902 = destruct_flex_t t1 in
                   let uu____17903 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17902 uu____17903
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17904,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17905;
                     FStar_Syntax_Syntax.pos = uu____17906;
                     FStar_Syntax_Syntax.vars = uu____17907;_},uu____17908))
                   ->
                   let uu____17961 = destruct_flex_t t1 in
                   let uu____17962 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17961 uu____17962
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17963;
                     FStar_Syntax_Syntax.pos = uu____17964;
                     FStar_Syntax_Syntax.vars = uu____17965;_},uu____17966),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17967;
                     FStar_Syntax_Syntax.pos = uu____17968;
                     FStar_Syntax_Syntax.vars = uu____17969;_},uu____17970))
                   ->
                   let uu____18043 = destruct_flex_t t1 in
                   let uu____18044 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18043 uu____18044
               | (FStar_Syntax_Syntax.Tm_uvar uu____18045,uu____18046) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18063 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18063 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18070;
                     FStar_Syntax_Syntax.pos = uu____18071;
                     FStar_Syntax_Syntax.vars = uu____18072;_},uu____18073),uu____18074)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18111 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18111 t2 wl
               | (uu____18118,FStar_Syntax_Syntax.Tm_uvar uu____18119) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18136,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18137;
                     FStar_Syntax_Syntax.pos = uu____18138;
                     FStar_Syntax_Syntax.vars = uu____18139;_},uu____18140))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18177,FStar_Syntax_Syntax.Tm_type uu____18178) ->
                   solve_t' env
                     (let uu___204_18196 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18196.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18196.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18196.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18196.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18196.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18196.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18196.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18196.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18196.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18197;
                     FStar_Syntax_Syntax.pos = uu____18198;
                     FStar_Syntax_Syntax.vars = uu____18199;_},uu____18200),FStar_Syntax_Syntax.Tm_type
                  uu____18201) ->
                   solve_t' env
                     (let uu___204_18239 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18239.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18239.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18239.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18239.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18239.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18239.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18239.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18239.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18239.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18240,FStar_Syntax_Syntax.Tm_arrow uu____18241) ->
                   solve_t' env
                     (let uu___204_18271 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18271.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18271.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18271.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18271.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18271.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18271.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18271.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18271.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18271.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18272;
                     FStar_Syntax_Syntax.pos = uu____18273;
                     FStar_Syntax_Syntax.vars = uu____18274;_},uu____18275),FStar_Syntax_Syntax.Tm_arrow
                  uu____18276) ->
                   solve_t' env
                     (let uu___204_18326 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___204_18326.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___204_18326.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___204_18326.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___204_18326.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___204_18326.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___204_18326.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___204_18326.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___204_18326.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___204_18326.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18327,uu____18328) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18347 =
                        let uu____18348 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18348 in
                      if uu____18347
                      then
                        let uu____18349 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___205_18355 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18355.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18355.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18355.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18355.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18355.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18355.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18355.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18355.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18355.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18356 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18349 uu____18356 t2
                          wl
                      else
                        (let uu____18364 = base_and_refinement env t2 in
                         match uu____18364 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18393 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___206_18399 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18399.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18399.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18399.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18399.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18399.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18399.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18399.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18399.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18399.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18400 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18393
                                    uu____18400 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18414 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18414.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18414.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18417 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18417 in
                                  let guard =
                                    let uu____18429 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18429
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18437;
                     FStar_Syntax_Syntax.pos = uu____18438;
                     FStar_Syntax_Syntax.vars = uu____18439;_},uu____18440),uu____18441)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18480 =
                        let uu____18481 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18481 in
                      if uu____18480
                      then
                        let uu____18482 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___205_18488 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___205_18488.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___205_18488.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___205_18488.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___205_18488.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___205_18488.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___205_18488.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___205_18488.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___205_18488.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___205_18488.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18489 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18482 uu____18489 t2
                          wl
                      else
                        (let uu____18497 = base_and_refinement env t2 in
                         match uu____18497 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18526 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___206_18532 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___206_18532.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___206_18532.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___206_18532.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___206_18532.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___206_18532.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___206_18532.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___206_18532.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___206_18532.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___206_18532.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18533 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18526
                                    uu____18533 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___207_18547 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___207_18547.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___207_18547.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18550 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18550 in
                                  let guard =
                                    let uu____18562 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18562
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18570,FStar_Syntax_Syntax.Tm_uvar uu____18571) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18589 = base_and_refinement env t1 in
                      match uu____18589 with
                      | (t_base,uu____18601) ->
                          solve_t env
                            (let uu___208_18615 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_18615.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_18615.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_18615.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_18615.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_18615.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_18615.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_18615.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_18615.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18616,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18617;
                     FStar_Syntax_Syntax.pos = uu____18618;
                     FStar_Syntax_Syntax.vars = uu____18619;_},uu____18620))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18658 = base_and_refinement env t1 in
                      match uu____18658 with
                      | (t_base,uu____18670) ->
                          solve_t env
                            (let uu___208_18684 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___208_18684.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___208_18684.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___208_18684.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___208_18684.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___208_18684.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___208_18684.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___208_18684.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___208_18684.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18685,uu____18686) ->
                   let t21 =
                     let uu____18696 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18696 in
                   solve_t env
                     (let uu___209_18720 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___209_18720.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___209_18720.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___209_18720.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___209_18720.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___209_18720.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___209_18720.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___209_18720.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___209_18720.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___209_18720.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18721,FStar_Syntax_Syntax.Tm_refine uu____18722) ->
                   let t11 =
                     let uu____18732 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18732 in
                   solve_t env
                     (let uu___210_18756 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___210_18756.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___210_18756.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___210_18756.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___210_18756.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___210_18756.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___210_18756.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___210_18756.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___210_18756.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___210_18756.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18759,uu____18760) ->
                   let head1 =
                     let uu____18786 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18786
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18830 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18830
                       FStar_Pervasives_Native.fst in
                   let uu____18871 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18871
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18886 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18886
                      then
                        let guard =
                          let uu____18898 =
                            let uu____18899 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18899 = FStar_Syntax_Util.Equal in
                          if uu____18898
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18903 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18903) in
                        let uu____18906 = solve_prob orig guard [] wl in
                        solve env uu____18906
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18909,uu____18910) ->
                   let head1 =
                     let uu____18920 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18920
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18964 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18964
                       FStar_Pervasives_Native.fst in
                   let uu____19005 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19005
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19020 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19020
                      then
                        let guard =
                          let uu____19032 =
                            let uu____19033 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19033 = FStar_Syntax_Util.Equal in
                          if uu____19032
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19037 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____19037) in
                        let uu____19040 = solve_prob orig guard [] wl in
                        solve env uu____19040
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19043,uu____19044) ->
                   let head1 =
                     let uu____19048 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19048
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19092 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19092
                       FStar_Pervasives_Native.fst in
                   let uu____19133 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19133
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19148 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19148
                      then
                        let guard =
                          let uu____19160 =
                            let uu____19161 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19161 = FStar_Syntax_Util.Equal in
                          if uu____19160
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19165 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19165) in
                        let uu____19168 = solve_prob orig guard [] wl in
                        solve env uu____19168
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19171,uu____19172) ->
                   let head1 =
                     let uu____19176 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19176
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19220 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19220
                       FStar_Pervasives_Native.fst in
                   let uu____19261 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19261
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19276 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19276
                      then
                        let guard =
                          let uu____19288 =
                            let uu____19289 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19289 = FStar_Syntax_Util.Equal in
                          if uu____19288
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19293 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19293) in
                        let uu____19296 = solve_prob orig guard [] wl in
                        solve env uu____19296
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19299,uu____19300) ->
                   let head1 =
                     let uu____19304 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19304
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19348 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19348
                       FStar_Pervasives_Native.fst in
                   let uu____19389 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19389
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19404 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19404
                      then
                        let guard =
                          let uu____19416 =
                            let uu____19417 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19417 = FStar_Syntax_Util.Equal in
                          if uu____19416
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19421 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19421) in
                        let uu____19424 = solve_prob orig guard [] wl in
                        solve env uu____19424
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19427,uu____19428) ->
                   let head1 =
                     let uu____19446 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19446
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19490 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19490
                       FStar_Pervasives_Native.fst in
                   let uu____19531 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19531
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19546 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19546
                      then
                        let guard =
                          let uu____19558 =
                            let uu____19559 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19559 = FStar_Syntax_Util.Equal in
                          if uu____19558
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19563 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19563) in
                        let uu____19566 = solve_prob orig guard [] wl in
                        solve env uu____19566
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19569,FStar_Syntax_Syntax.Tm_match uu____19570) ->
                   let head1 =
                     let uu____19596 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19596
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19640 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19640
                       FStar_Pervasives_Native.fst in
                   let uu____19681 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19681
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19696 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19696
                      then
                        let guard =
                          let uu____19708 =
                            let uu____19709 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19709 = FStar_Syntax_Util.Equal in
                          if uu____19708
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19713 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19713) in
                        let uu____19716 = solve_prob orig guard [] wl in
                        solve env uu____19716
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19719,FStar_Syntax_Syntax.Tm_uinst uu____19720) ->
                   let head1 =
                     let uu____19730 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19730
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19774 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19774
                       FStar_Pervasives_Native.fst in
                   let uu____19815 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19815
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19830 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19830
                      then
                        let guard =
                          let uu____19842 =
                            let uu____19843 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19843 = FStar_Syntax_Util.Equal in
                          if uu____19842
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19847 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19847) in
                        let uu____19850 = solve_prob orig guard [] wl in
                        solve env uu____19850
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19853,FStar_Syntax_Syntax.Tm_name uu____19854) ->
                   let head1 =
                     let uu____19858 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19858
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19902 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19902
                       FStar_Pervasives_Native.fst in
                   let uu____19943 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19943
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19958 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19958
                      then
                        let guard =
                          let uu____19970 =
                            let uu____19971 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19971 = FStar_Syntax_Util.Equal in
                          if uu____19970
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19975 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19975) in
                        let uu____19978 = solve_prob orig guard [] wl in
                        solve env uu____19978
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19981,FStar_Syntax_Syntax.Tm_constant uu____19982) ->
                   let head1 =
                     let uu____19986 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19986
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20030 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20030
                       FStar_Pervasives_Native.fst in
                   let uu____20071 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20071
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20086 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20086
                      then
                        let guard =
                          let uu____20098 =
                            let uu____20099 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20099 = FStar_Syntax_Util.Equal in
                          if uu____20098
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20103 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20103) in
                        let uu____20106 = solve_prob orig guard [] wl in
                        solve env uu____20106
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20109,FStar_Syntax_Syntax.Tm_fvar uu____20110) ->
                   let head1 =
                     let uu____20114 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20114
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20158 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20158
                       FStar_Pervasives_Native.fst in
                   let uu____20199 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20199
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20214 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20214
                      then
                        let guard =
                          let uu____20226 =
                            let uu____20227 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20227 = FStar_Syntax_Util.Equal in
                          if uu____20226
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20231 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20231) in
                        let uu____20234 = solve_prob orig guard [] wl in
                        solve env uu____20234
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20237,FStar_Syntax_Syntax.Tm_app uu____20238) ->
                   let head1 =
                     let uu____20256 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20256
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20300 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20300
                       FStar_Pervasives_Native.fst in
                   let uu____20341 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20341
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20356 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20356
                      then
                        let guard =
                          let uu____20368 =
                            let uu____20369 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20369 = FStar_Syntax_Util.Equal in
                          if uu____20368
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20373 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20373) in
                        let uu____20376 = solve_prob orig guard [] wl in
                        solve env uu____20376
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20379,uu____20380) ->
                   let uu____20393 =
                     let uu____20394 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20395 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20394
                       uu____20395 in
                   failwith uu____20393
               | (FStar_Syntax_Syntax.Tm_delayed uu____20396,uu____20397) ->
                   let uu____20422 =
                     let uu____20423 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20424 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20423
                       uu____20424 in
                   failwith uu____20422
               | (uu____20425,FStar_Syntax_Syntax.Tm_delayed uu____20426) ->
                   let uu____20451 =
                     let uu____20452 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20453 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20452
                       uu____20453 in
                   failwith uu____20451
               | (uu____20454,FStar_Syntax_Syntax.Tm_let uu____20455) ->
                   let uu____20468 =
                     let uu____20469 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20470 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20469
                       uu____20470 in
                   failwith uu____20468
               | uu____20471 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20507 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20507
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20509 =
               let uu____20510 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20511 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20510 uu____20511 in
             giveup env uu____20509 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20531  ->
                    fun uu____20532  ->
                      match (uu____20531, uu____20532) with
                      | ((a1,uu____20550),(a2,uu____20552)) ->
                          let uu____20561 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20561)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20571 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20571 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20595 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20602)::[] -> wp1
              | uu____20619 ->
                  let uu____20628 =
                    let uu____20629 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20629 in
                  failwith uu____20628 in
            let uu____20632 =
              let uu____20641 =
                let uu____20642 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20642 in
              [uu____20641] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20632;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20643 = lift_c1 () in solve_eq uu____20643 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___164_20649  ->
                       match uu___164_20649 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20650 -> false)) in
             let uu____20651 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20685)::uu____20686,(wp2,uu____20688)::uu____20689)
                   -> (wp1, wp2)
               | uu____20746 ->
                   let uu____20767 =
                     let uu____20768 =
                       let uu____20773 =
                         let uu____20774 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20775 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20774 uu____20775 in
                       (uu____20773, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20768 in
                   FStar_Exn.raise uu____20767 in
             match uu____20651 with
             | (wpc1,wpc2) ->
                 let uu____20794 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20794
                 then
                   let uu____20797 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20797 wl
                 else
                   (let uu____20801 =
                      let uu____20808 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20808 in
                    match uu____20801 with
                    | (c2_decl,qualifiers) ->
                        let uu____20829 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20829
                        then
                          let c1_repr =
                            let uu____20833 =
                              let uu____20834 =
                                let uu____20835 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20835 in
                              let uu____20836 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20834 uu____20836 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20833 in
                          let c2_repr =
                            let uu____20838 =
                              let uu____20839 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20840 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20839 uu____20840 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20838 in
                          let prob =
                            let uu____20842 =
                              let uu____20847 =
                                let uu____20848 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20849 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20848
                                  uu____20849 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20847 in
                            FStar_TypeChecker_Common.TProb uu____20842 in
                          let wl1 =
                            let uu____20851 =
                              let uu____20854 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20854 in
                            solve_prob orig uu____20851 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20863 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20863
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____20865 =
                                     let uu____20868 =
                                       let uu____20869 =
                                         let uu____20884 =
                                           let uu____20885 =
                                             let uu____20886 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____20886] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____20885 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20887 =
                                           let uu____20890 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20891 =
                                             let uu____20894 =
                                               let uu____20895 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20895 in
                                             [uu____20894] in
                                           uu____20890 :: uu____20891 in
                                         (uu____20884, uu____20887) in
                                       FStar_Syntax_Syntax.Tm_app uu____20869 in
                                     FStar_Syntax_Syntax.mk uu____20868 in
                                   uu____20865 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____20902 =
                                    let uu____20905 =
                                      let uu____20906 =
                                        let uu____20921 =
                                          let uu____20922 =
                                            let uu____20923 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____20923] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____20922 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20924 =
                                          let uu____20927 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20928 =
                                            let uu____20931 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20932 =
                                              let uu____20935 =
                                                let uu____20936 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20936 in
                                              [uu____20935] in
                                            uu____20931 :: uu____20932 in
                                          uu____20927 :: uu____20928 in
                                        (uu____20921, uu____20924) in
                                      FStar_Syntax_Syntax.Tm_app uu____20906 in
                                    FStar_Syntax_Syntax.mk uu____20905 in
                                  uu____20902 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20943 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20943 in
                           let wl1 =
                             let uu____20953 =
                               let uu____20956 =
                                 let uu____20959 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20959 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20956 in
                             solve_prob orig uu____20953 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20972 = FStar_Util.physical_equality c1 c2 in
        if uu____20972
        then
          let uu____20973 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20973
        else
          ((let uu____20976 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20976
            then
              let uu____20977 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20978 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20977
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20978
            else ());
           (let uu____20980 =
              let uu____20985 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20986 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20985, uu____20986) in
            match uu____20980 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20990),FStar_Syntax_Syntax.Total
                    (t2,uu____20992)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21009 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21009 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21012,FStar_Syntax_Syntax.Total uu____21013) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21031),FStar_Syntax_Syntax.Total
                    (t2,uu____21033)) ->
                     let uu____21050 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21050 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21054),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21056)) ->
                     let uu____21073 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21073 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21077),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21079)) ->
                     let uu____21096 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21096 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21099,FStar_Syntax_Syntax.Comp uu____21100) ->
                     let uu____21109 =
                       let uu___211_21114 = problem in
                       let uu____21119 =
                         let uu____21120 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21120 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21114.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21119;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21114.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21114.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21114.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21114.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21114.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21114.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21114.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21114.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21109 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21121,FStar_Syntax_Syntax.Comp uu____21122) ->
                     let uu____21131 =
                       let uu___211_21136 = problem in
                       let uu____21141 =
                         let uu____21142 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21142 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___211_21136.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21141;
                         FStar_TypeChecker_Common.relation =
                           (uu___211_21136.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___211_21136.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___211_21136.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___211_21136.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___211_21136.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___211_21136.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___211_21136.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___211_21136.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21131 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21143,FStar_Syntax_Syntax.GTotal uu____21144) ->
                     let uu____21153 =
                       let uu___212_21158 = problem in
                       let uu____21163 =
                         let uu____21164 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21164 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21158.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21158.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21158.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21163;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21158.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21158.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21158.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21158.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21158.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21158.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21153 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21165,FStar_Syntax_Syntax.Total uu____21166) ->
                     let uu____21175 =
                       let uu___212_21180 = problem in
                       let uu____21185 =
                         let uu____21186 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21186 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___212_21180.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___212_21180.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___212_21180.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21185;
                         FStar_TypeChecker_Common.element =
                           (uu___212_21180.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___212_21180.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___212_21180.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___212_21180.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___212_21180.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___212_21180.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21175 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21187,FStar_Syntax_Syntax.Comp uu____21188) ->
                     let uu____21189 =
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
                     if uu____21189
                     then
                       let uu____21190 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21190 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21196 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21206 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21207 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21206, uu____21207)) in
                          match uu____21196 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21214 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21214
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21216 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21216 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21219 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21221 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21221) in
                                if uu____21219
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
                                  (let uu____21224 =
                                     let uu____21225 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21226 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21225 uu____21226 in
                                   giveup env uu____21224 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21232 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21270  ->
              match uu____21270 with
              | (uu____21283,uu____21284,u,uu____21286,uu____21287,uu____21288)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21232 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21320 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21320 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21338 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21366  ->
                match uu____21366 with
                | (u1,u2) ->
                    let uu____21373 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21374 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21373 uu____21374)) in
      FStar_All.pipe_right uu____21338 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21393,[])) -> "{}"
      | uu____21418 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21435 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21435
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21438 =
              FStar_List.map
                (fun uu____21448  ->
                   match uu____21448 with
                   | (uu____21453,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21438 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21458 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21458 imps
let new_t_problem:
  'Auu____21473 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21473 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21473)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21507 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21507
                then
                  let uu____21508 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21509 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21508
                    (rel_to_string rel) uu____21509
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
            let uu____21537 =
              let uu____21540 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21540 in
            FStar_Syntax_Syntax.new_bv uu____21537 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21549 =
              let uu____21552 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21552 in
            let uu____21555 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21549 uu____21555 in
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
          let uu____21588 = FStar_Options.eager_inference () in
          if uu____21588
          then
            let uu___213_21589 = probs in
            {
              attempting = (uu___213_21589.attempting);
              wl_deferred = (uu___213_21589.wl_deferred);
              ctr = (uu___213_21589.ctr);
              defer_ok = false;
              smt_ok = (uu___213_21589.smt_ok);
              tcenv = (uu___213_21589.tcenv)
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
             (let uu____21601 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21601
              then
                let uu____21602 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21602
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
          ((let uu____21614 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21614
            then
              let uu____21615 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21615
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21619 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21619
             then
               let uu____21620 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21620
             else ());
            (let f2 =
               let uu____21623 =
                 let uu____21624 = FStar_Syntax_Util.unmeta f1 in
                 uu____21624.FStar_Syntax_Syntax.n in
               match uu____21623 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21628 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___214_21629 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___214_21629.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___214_21629.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___214_21629.FStar_TypeChecker_Env.implicits)
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
            let uu____21651 =
              let uu____21652 =
                let uu____21653 =
                  let uu____21654 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21654
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21653;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21652 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21651
let with_guard_no_simp:
  'Auu____21685 .
    'Auu____21685 ->
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
            let uu____21705 =
              let uu____21706 =
                let uu____21707 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21707
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21706;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21705
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
          (let uu____21749 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21749
           then
             let uu____21750 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21751 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21750
               uu____21751
           else ());
          (let prob =
             let uu____21754 =
               let uu____21759 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21759 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21754 in
           let g =
             let uu____21767 =
               let uu____21770 = singleton' env prob smt_ok in
               solve_and_commit env uu____21770
                 (fun uu____21772  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21767 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21793 = try_teq true env t1 t2 in
        match uu____21793 with
        | FStar_Pervasives_Native.None  ->
            let uu____21796 =
              let uu____21797 =
                let uu____21802 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21803 = FStar_TypeChecker_Env.get_range env in
                (uu____21802, uu____21803) in
              FStar_Errors.Error uu____21797 in
            FStar_Exn.raise uu____21796
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21806 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21806
              then
                let uu____21807 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21808 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21809 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21807
                  uu____21808 uu____21809
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
          (let uu____21830 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21830
           then
             let uu____21831 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21832 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21831
               uu____21832
           else ());
          (let uu____21834 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21834 with
           | (prob,x) ->
               let g =
                 let uu____21846 =
                   let uu____21849 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21849
                     (fun uu____21851  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21846 in
               ((let uu____21861 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____21861
                 then
                   let uu____21862 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____21863 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____21864 =
                     let uu____21865 = FStar_Util.must g in
                     guard_to_string env uu____21865 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____21862 uu____21863 uu____21864
                 else ());
                (let uu____21867 =
                   let uu____21870 = FStar_Syntax_Syntax.mk_binder x in
                   abstract_guard uu____21870 in
                 FStar_Util.map_opt g uu____21867)))
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
          let uu____21901 = FStar_TypeChecker_Env.get_range env in
          let uu____21902 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21901 uu____21902
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21918 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21918
         then
           let uu____21919 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21920 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21919
             uu____21920
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21925 =
             let uu____21930 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21930 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21925 in
         let uu____21935 =
           let uu____21938 = singleton env prob in
           solve_and_commit env uu____21938
             (fun uu____21940  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21935)
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
      fun uu____21972  ->
        match uu____21972 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22011 =
                 let uu____22012 =
                   let uu____22017 =
                     let uu____22018 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____22019 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____22018 uu____22019 in
                   let uu____22020 = FStar_TypeChecker_Env.get_range env in
                   (uu____22017, uu____22020) in
                 FStar_Errors.Error uu____22012 in
               FStar_Exn.raise uu____22011) in
            let equiv1 v1 v' =
              let uu____22028 =
                let uu____22033 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22034 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22033, uu____22034) in
              match uu____22028 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22053 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22083 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22083 with
                      | FStar_Syntax_Syntax.U_unif uu____22090 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22119  ->
                                    match uu____22119 with
                                    | (u,v') ->
                                        let uu____22128 = equiv1 v1 v' in
                                        if uu____22128
                                        then
                                          let uu____22131 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22131 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22147 -> [])) in
            let uu____22152 =
              let wl =
                let uu___215_22156 = empty_worklist env in
                {
                  attempting = (uu___215_22156.attempting);
                  wl_deferred = (uu___215_22156.wl_deferred);
                  ctr = (uu___215_22156.ctr);
                  defer_ok = false;
                  smt_ok = (uu___215_22156.smt_ok);
                  tcenv = (uu___215_22156.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22174  ->
                      match uu____22174 with
                      | (lb,v1) ->
                          let uu____22181 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22181 with
                           | USolved wl1 -> ()
                           | uu____22183 -> fail lb v1))) in
            let rec check_ineq uu____22191 =
              match uu____22191 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22200) -> true
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
                      uu____22223,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22225,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22236) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22243,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22251 -> false) in
            let uu____22256 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22271  ->
                      match uu____22271 with
                      | (u,v1) ->
                          let uu____22278 = check_ineq (u, v1) in
                          if uu____22278
                          then true
                          else
                            ((let uu____22281 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22281
                              then
                                let uu____22282 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22283 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22282
                                  uu____22283
                              else ());
                             false))) in
            if uu____22256
            then ()
            else
              ((let uu____22287 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22287
                then
                  ((let uu____22289 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22289);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22299 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22299))
                else ());
               (let uu____22309 =
                  let uu____22310 =
                    let uu____22315 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22315) in
                  FStar_Errors.Error uu____22310 in
                FStar_Exn.raise uu____22309))
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
      let fail uu____22367 =
        match uu____22367 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22381 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22381
       then
         let uu____22382 = wl_to_string wl in
         let uu____22383 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22382 uu____22383
       else ());
      (let g1 =
         let uu____22398 = solve_and_commit env wl fail in
         match uu____22398 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___216_22411 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___216_22411.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___216_22411.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___216_22411.FStar_TypeChecker_Env.implicits)
             }
         | uu____22416 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___217_22420 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___217_22420.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___217_22420.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___217_22420.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22443 = FStar_ST.op_Bang last_proof_ns in
    match uu____22443 with
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
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac")) in
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___218_22631 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___218_22631.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___218_22631.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___218_22631.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22632 =
            let uu____22633 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22633 in
          if uu____22632
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22641 = FStar_TypeChecker_Env.get_range env in
                     let uu____22642 =
                       let uu____22643 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22643 in
                     FStar_Errors.diag uu____22641 uu____22642)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22647 = FStar_TypeChecker_Env.get_range env in
                      let uu____22648 =
                        let uu____22649 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22649 in
                      FStar_Errors.diag uu____22647 uu____22648)
                   else ();
                   (let uu____22651 = check_trivial vc1 in
                    match uu____22651 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22658 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22659 =
                                let uu____22660 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22660 in
                              FStar_Errors.diag uu____22658 uu____22659)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22665 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22666 =
                                let uu____22667 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22667 in
                              FStar_Errors.diag uu____22665 uu____22666)
                           else ();
                           (let vcs =
                              let uu____22678 = FStar_Options.use_tactics () in
                              if uu____22678
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22697  ->
                                     (let uu____22699 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22699);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22701 =
                                   let uu____22708 = FStar_Options.peek () in
                                   (env, vc2, uu____22708) in
                                 [uu____22701]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22742  ->
                                    match uu____22742 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22753 = check_trivial goal1 in
                                        (match uu____22753 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal2 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____22761 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22762 =
                                                   let uu____22763 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22764 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22763 uu____22764 in
                                                 FStar_Errors.diag
                                                   uu____22761 uu____22762)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22767 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22768 =
                                                   let uu____22769 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22769 in
                                                 FStar_Errors.diag
                                                   uu____22767 uu____22768)
                                              else ();
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
      let uu____22781 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22781 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22787 =
            let uu____22788 =
              let uu____22793 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22793) in
            FStar_Errors.Error uu____22788 in
          FStar_Exn.raise uu____22787
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22802 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22802 with
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
          let uu____22824 = FStar_Syntax_Unionfind.find u in
          match uu____22824 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22827 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22845 = acc in
          match uu____22845 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22931 = hd1 in
                   (match uu____22931 with
                    | (uu____22944,env,u,tm,k,r) ->
                        let uu____22950 = unresolved u in
                        if uu____22950
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22981 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22981
                            then
                              let uu____22982 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22983 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22984 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22982 uu____22983 uu____22984
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___219_22987 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___219_22987.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___219_22987.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___219_22987.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___219_22987.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___219_22987.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___219_22987.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___219_22987.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___219_22987.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___219_22987.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___219_22987.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___219_22987.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___219_22987.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___219_22987.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___219_22987.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___219_22987.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___219_22987.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___219_22987.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___219_22987.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___219_22987.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___219_22987.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___219_22987.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___219_22987.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___219_22987.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___219_22987.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___219_22987.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___219_22987.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___219_22987.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___219_22987.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___219_22987.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___219_22987.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___219_22987.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___219_22987.FStar_TypeChecker_Env.dsenv)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____22990 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___220_22998 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___220_22998.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___220_22998.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___220_22998.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___220_22998.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___220_22998.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___220_22998.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___220_22998.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___220_22998.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___220_22998.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___220_22998.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___220_22998.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___220_22998.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___220_22998.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___220_22998.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___220_22998.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___220_22998.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___220_22998.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___220_22998.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___220_22998.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___220_22998.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___220_22998.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___220_22998.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___220_22998.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___220_22998.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___220_22998.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___220_22998.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___220_22998.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___220_22998.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___220_22998.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___220_22998.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___220_22998.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___220_22998.FStar_TypeChecker_Env.dsenv)
                                     }) tm1 in
                                match uu____22990 with
                                | (uu____22999,uu____23000,g1) -> g1
                              else
                                (let uu____23003 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___221_23011 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___221_23011.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___221_23011.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___221_23011.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___221_23011.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___221_23011.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___221_23011.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___221_23011.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___221_23011.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___221_23011.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___221_23011.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___221_23011.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___221_23011.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___221_23011.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___221_23011.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___221_23011.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___221_23011.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___221_23011.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___221_23011.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___221_23011.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___221_23011.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___221_23011.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___221_23011.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___221_23011.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___221_23011.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___221_23011.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___221_23011.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___221_23011.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___221_23011.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___221_23011.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___221_23011.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___221_23011.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___221_23011.FStar_TypeChecker_Env.dsenv)
                                      }) tm1 in
                                 match uu____23003 with
                                 | (uu____23012,uu____23013,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___222_23016 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___222_23016.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___222_23016.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___222_23016.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23019 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23025  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23019 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___223_23053 = g in
        let uu____23054 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___223_23053.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___223_23053.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___223_23053.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23054
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
        let uu____23112 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23112 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23125 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23125
      | (reason,uu____23127,uu____23128,e,t,r)::uu____23132 ->
          let uu____23159 =
            let uu____23160 =
              let uu____23165 =
                let uu____23166 = FStar_Syntax_Print.term_to_string t in
                let uu____23167 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____23166 uu____23167 in
              (uu____23165, r) in
            FStar_Errors.Error uu____23160 in
          FStar_Exn.raise uu____23159
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___224_23176 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___224_23176.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___224_23176.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___224_23176.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23205 = try_teq false env t1 t2 in
        match uu____23205 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____23209 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____23209 with
             | FStar_Pervasives_Native.Some uu____23214 -> true
             | FStar_Pervasives_Native.None  -> false)