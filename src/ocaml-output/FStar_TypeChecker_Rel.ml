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
          let uu___305_91 = g in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___305_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___305_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___305_91.FStar_TypeChecker_Env.implicits)
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
        let uu____121 = FStar_Util.set_is_empty s in
        if uu____121
        then ()
        else
          (let uu____123 =
             let uu____124 =
               let uu____125 =
                 let uu____126 =
                   let uu____129 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____129
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____126
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format2 "Guard has free variables (%s): %s" msg
                 uu____125 in
             FStar_Errors.Err uu____124 in
           FStar_Exn.raise uu____123)
let check_term:
  Prims.string ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun msg  ->
    fun env  ->
      fun t  ->
        let s = FStar_TypeChecker_Env.unbound_vars env t in
        let uu____150 = FStar_Util.set_is_empty s in
        if uu____150
        then ()
        else
          (let uu____152 =
             let uu____153 =
               let uu____154 = FStar_Syntax_Print.term_to_string t in
               let uu____155 =
                 let uu____156 =
                   let uu____159 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____159
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____156
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format3 "Term <%s> has free variables (%s): %s"
                 uu____154 msg uu____155 in
             FStar_Errors.Err uu____153 in
           FStar_Exn.raise uu____152)
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___306_175 = g in
          let uu____176 =
            let uu____177 =
              let uu____178 =
                let uu____181 =
                  let uu____182 =
                    let uu____197 =
                      let uu____200 = FStar_Syntax_Syntax.as_arg e in
                      [uu____200] in
                    (f, uu____197) in
                  FStar_Syntax_Syntax.Tm_app uu____182 in
                FStar_Syntax_Syntax.mk uu____181 in
              uu____178 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____177 in
          {
            FStar_TypeChecker_Env.guard_f = uu____176;
            FStar_TypeChecker_Env.deferred =
              (uu___306_175.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___306_175.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___306_175.FStar_TypeChecker_Env.implicits)
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
          let uu___307_218 = g in
          let uu____219 =
            let uu____220 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____220 in
          {
            FStar_TypeChecker_Env.guard_f = uu____219;
            FStar_TypeChecker_Env.deferred =
              (uu___307_218.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___307_218.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___307_218.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____224 -> failwith "impossible"
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
          let uu____235 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____235
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____239 =
      let uu____240 = FStar_Syntax_Util.unmeta t in
      uu____240.FStar_Syntax_Syntax.n in
    match uu____239 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____244 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____275 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____275;
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
                       let uu____342 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____342
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___308_344 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___308_344.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___308_344.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___308_344.FStar_TypeChecker_Env.implicits)
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
               let uu____363 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____363
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
            let uu___309_376 = g in
            let uu____377 =
              let uu____378 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____378 in
            {
              FStar_TypeChecker_Env.guard_f = uu____377;
              FStar_TypeChecker_Env.deferred =
                (uu___309_376.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___309_376.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___309_376.FStar_TypeChecker_Env.implicits)
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
        | uu____408 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____433 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____433 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____441 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____441, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____469 = FStar_Syntax_Util.type_u () in
        match uu____469 with
        | (t_type,u) ->
            let uu____476 =
              let uu____481 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____481 t_type in
            (match uu____476 with
             | (tt,uu____483) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____516 -> false
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
    match projectee with | Success _0 -> true | uu____742 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____758 -> false
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
    match projectee with | COVARIANT  -> true | uu____781 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____785 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____789 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___277_812  ->
    match uu___277_812 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____818 =
        let uu____819 = FStar_Syntax_Subst.compress t in
        uu____819.FStar_Syntax_Syntax.n in
      match uu____818 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____848 = FStar_Syntax_Print.uvar_to_string u in
          let uu____849 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____848 uu____849
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____852;
             FStar_Syntax_Syntax.vars = uu____853;_},args)
          ->
          let uu____899 = FStar_Syntax_Print.uvar_to_string u in
          let uu____900 = FStar_Syntax_Print.term_to_string ty in
          let uu____901 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____899 uu____900 uu____901
      | uu____902 -> "--" in
    let uu____903 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____903 detail
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___278_909  ->
      match uu___278_909 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____915 =
            let uu____918 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____919 =
              let uu____922 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____923 =
                let uu____926 =
                  let uu____929 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____929] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____926 in
              uu____922 :: uu____923 in
            uu____918 :: uu____919 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____915
      | FStar_TypeChecker_Common.CProb p ->
          let uu____935 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____936 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____935
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____936
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___279_942  ->
      match uu___279_942 with
      | UNIV (u,t) ->
          let x =
            let uu____946 = FStar_Options.hide_uvar_nums () in
            if uu____946
            then "?"
            else
              (let uu____948 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____948 FStar_Util.string_of_int) in
          let uu____949 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____949
      | TERM ((u,uu____951),t) ->
          let x =
            let uu____958 = FStar_Options.hide_uvar_nums () in
            if uu____958
            then "?"
            else
              (let uu____960 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____960 FStar_Util.string_of_int) in
          let uu____961 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____961
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____972 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____972 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____984 =
      let uu____987 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____987
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____984 (FStar_String.concat ", ")
let args_to_string:
  'Auu____998 .
    (FStar_Syntax_Syntax.term,'Auu____998) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1015 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1033  ->
              match uu____1033 with
              | (x,uu____1039) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1015 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1045 =
      let uu____1046 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1046 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1045;
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
        let uu___310_1062 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___310_1062.wl_deferred);
          ctr = (uu___310_1062.ctr);
          defer_ok = (uu___310_1062.defer_ok);
          smt_ok;
          tcenv = (uu___310_1062.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1072 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1072,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___311_1093 = empty_worklist env in
      let uu____1094 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1094;
        wl_deferred = (uu___311_1093.wl_deferred);
        ctr = (uu___311_1093.ctr);
        defer_ok = false;
        smt_ok = (uu___311_1093.smt_ok);
        tcenv = (uu___311_1093.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___312_1108 = wl in
        {
          attempting = (uu___312_1108.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___312_1108.ctr);
          defer_ok = (uu___312_1108.defer_ok);
          smt_ok = (uu___312_1108.smt_ok);
          tcenv = (uu___312_1108.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___313_1125 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___313_1125.wl_deferred);
        ctr = (uu___313_1125.ctr);
        defer_ok = (uu___313_1125.defer_ok);
        smt_ok = (uu___313_1125.smt_ok);
        tcenv = (uu___313_1125.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1136 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1136
         then
           let uu____1137 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1137
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___280_1141  ->
    match uu___280_1141 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1145 'Auu____1146 .
    ('Auu____1146,'Auu____1145) FStar_TypeChecker_Common.problem ->
      ('Auu____1146,'Auu____1145) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___314_1163 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___314_1163.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___314_1163.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___314_1163.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___314_1163.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___314_1163.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___314_1163.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___314_1163.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1171 'Auu____1172 .
    ('Auu____1172,'Auu____1171) FStar_TypeChecker_Common.problem ->
      ('Auu____1172,'Auu____1171) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___281_1192  ->
    match uu___281_1192 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___282_1216  ->
      match uu___282_1216 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___283_1219  ->
    match uu___283_1219 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___284_1232  ->
    match uu___284_1232 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___285_1247  ->
    match uu___285_1247 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___286_1262  ->
    match uu___286_1262 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___287_1279  ->
    match uu___287_1279 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___288_1296  ->
    match uu___288_1296 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___289_1309  ->
    match uu___289_1309 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1331 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1331 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1343  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1435 'Auu____1436 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1436 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1436 ->
              'Auu____1435 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1436,'Auu____1435)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1473 = next_pid () in
                let uu____1474 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1473;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1474;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1488 'Auu____1489 .
    FStar_TypeChecker_Env.env ->
      'Auu____1489 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1489 ->
            'Auu____1488 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1489,'Auu____1488)
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
                let uu____1527 = next_pid () in
                let uu____1528 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1527;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1528;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1541 'Auu____1542 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1542 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1542 ->
            'Auu____1541 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1542,'Auu____1541) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1575 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1575;
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
  'Auu____1581 .
    worklist ->
      ('Auu____1581,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1631 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1631
        then
          let uu____1632 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1633 = prob_to_string env d in
          let uu____1634 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1632 uu____1633 uu____1634 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1640 -> failwith "impossible" in
           let uu____1641 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1655 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1656 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1655, uu____1656)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1662 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1663 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1662, uu____1663) in
           match uu____1641 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___290_1679  ->
            match uu___290_1679 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1691 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1693),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___291_1713  ->
           match uu___291_1713 with
           | UNIV uu____1716 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1722),t) ->
               let uu____1728 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1728
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
        (fun uu___292_1748  ->
           match uu___292_1748 with
           | UNIV (u',t) ->
               let uu____1753 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1753
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1757 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1764 =
        let uu____1765 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1765 in
      FStar_Syntax_Subst.compress uu____1764
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1772 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1772
let norm_arg:
  'Auu____1776 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1776) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1776)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1797 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1797, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1828  ->
              match uu____1828 with
              | (x,imp) ->
                  let uu____1839 =
                    let uu___315_1840 = x in
                    let uu____1841 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___315_1840.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___315_1840.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1841
                    } in
                  (uu____1839, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1856 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1856
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1860 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1860
        | uu____1863 -> u2 in
      let uu____1864 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1864
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
              (let uu____1956 =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               match uu____1956 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                     (x1,phi1);
                   FStar_Syntax_Syntax.pos = uu____1973;
                   FStar_Syntax_Syntax.vars = uu____1974;_} ->
                   ((x1.FStar_Syntax_Syntax.sort),
                     (FStar_Pervasives_Native.Some (x1, phi1)))
               | tt ->
                   let uu____2000 =
                     let uu____2001 = FStar_Syntax_Print.term_to_string tt in
                     let uu____2002 = FStar_Syntax_Print.tag_of_term tt in
                     FStar_Util.format2 "impossible: Got %s ... %s\n"
                       uu____2001 uu____2002 in
                   failwith uu____2000)
        | FStar_Syntax_Syntax.Tm_uinst uu____2017 ->
            if norm1
            then (t12, FStar_Pervasives_Native.None)
            else
              (let t1' =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               let uu____2054 =
                 let uu____2055 = FStar_Syntax_Subst.compress t1' in
                 uu____2055.FStar_Syntax_Syntax.n in
               match uu____2054 with
               | FStar_Syntax_Syntax.Tm_refine uu____2072 -> aux true t1'
               | uu____2079 -> (t12, FStar_Pervasives_Native.None))
        | FStar_Syntax_Syntax.Tm_fvar uu____2094 ->
            if norm1
            then (t12, FStar_Pervasives_Native.None)
            else
              (let t1' =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               let uu____2125 =
                 let uu____2126 = FStar_Syntax_Subst.compress t1' in
                 uu____2126.FStar_Syntax_Syntax.n in
               match uu____2125 with
               | FStar_Syntax_Syntax.Tm_refine uu____2143 -> aux true t1'
               | uu____2150 -> (t12, FStar_Pervasives_Native.None))
        | FStar_Syntax_Syntax.Tm_app uu____2165 ->
            if norm1
            then (t12, FStar_Pervasives_Native.None)
            else
              (let t1' =
                 FStar_TypeChecker_Normalize.normalize_refinement
                   [FStar_TypeChecker_Normalize.Weak;
                   FStar_TypeChecker_Normalize.HNF] env t12 in
               let uu____2210 =
                 let uu____2211 = FStar_Syntax_Subst.compress t1' in
                 uu____2211.FStar_Syntax_Syntax.n in
               match uu____2210 with
               | FStar_Syntax_Syntax.Tm_refine uu____2228 -> aux true t1'
               | uu____2235 -> (t12, FStar_Pervasives_Native.None))
        | FStar_Syntax_Syntax.Tm_type uu____2250 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_constant uu____2265 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_name uu____2280 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_bvar uu____2295 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_arrow uu____2310 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_abs uu____2337 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_uvar uu____2368 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_let uu____2399 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_match uu____2426 ->
            (t12, FStar_Pervasives_Native.None)
        | FStar_Syntax_Syntax.Tm_meta uu____2463 ->
            let uu____2470 =
              let uu____2471 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2472 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2471 uu____2472 in
            failwith uu____2470
        | FStar_Syntax_Syntax.Tm_ascribed uu____2487 ->
            let uu____2514 =
              let uu____2515 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2516 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2515 uu____2516 in
            failwith uu____2514
        | FStar_Syntax_Syntax.Tm_delayed uu____2531 ->
            let uu____2556 =
              let uu____2557 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2558 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2557 uu____2558 in
            failwith uu____2556
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2573 =
              let uu____2574 = FStar_Syntax_Print.term_to_string t12 in
              let uu____2575 = FStar_Syntax_Print.tag_of_term t12 in
              FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                uu____2574 uu____2575 in
            failwith uu____2573 in
      let uu____2590 = whnf env t1 in aux false uu____2590
let normalize_refinement:
  'Auu____2596 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2596 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2619 = base_and_refinement env t in
      FStar_All.pipe_right uu____2619 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2653 = FStar_Syntax_Syntax.null_bv t in
    (uu____2653, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2658 .
    FStar_TypeChecker_Env.env ->
      'Auu____2658 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2675 = base_and_refinement env t in
        match uu____2675 with
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
  fun uu____2732  ->
    match uu____2732 with
    | (t_base,refopt) ->
        let uu____2759 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2759 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2791 =
      let uu____2794 =
        let uu____2797 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2820  ->
                  match uu____2820 with | (uu____2827,uu____2828,x) -> x)) in
        FStar_List.append wl.attempting uu____2797 in
      FStar_List.map (wl_prob_to_string wl) uu____2794 in
    FStar_All.pipe_right uu____2791 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2841 =
          let uu____2854 =
            let uu____2855 = FStar_Syntax_Subst.compress k in
            uu____2855.FStar_Syntax_Syntax.n in
          match uu____2854 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2908 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2908)
              else
                (let uu____2922 = FStar_Syntax_Util.abs_formals t in
                 match uu____2922 with
                 | (ys',t1,uu____2945) ->
                     let uu____2950 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____2950))
          | uu____2991 ->
              let uu____2992 =
                let uu____3003 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3003) in
              ((ys, t), uu____2992) in
        match uu____2841 with
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
                 let uu____3052 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3052 c in
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
            let uu____3080 = p_guard prob in
            match uu____3080 with
            | (uu____3085,uv) ->
                ((let uu____3088 =
                    let uu____3089 = FStar_Syntax_Subst.compress uv in
                    uu____3089.FStar_Syntax_Syntax.n in
                  match uu____3088 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3121 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3121
                        then
                          let uu____3122 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3123 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3124 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3122
                            uu____3123 uu____3124
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3126 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___316_3129 = wl in
                  {
                    attempting = (uu___316_3129.attempting);
                    wl_deferred = (uu___316_3129.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___316_3129.defer_ok);
                    smt_ok = (uu___316_3129.smt_ok);
                    tcenv = (uu___316_3129.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3144 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3144
         then
           let uu____3145 = FStar_Util.string_of_int pid in
           let uu____3146 =
             let uu____3147 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3147 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3145 uu____3146
         else ());
        commit sol;
        (let uu___317_3154 = wl in
         {
           attempting = (uu___317_3154.attempting);
           wl_deferred = (uu___317_3154.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___317_3154.defer_ok);
           smt_ok = (uu___317_3154.smt_ok);
           tcenv = (uu___317_3154.tcenv)
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
            | (uu____3192,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3204 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3204 in
          (let uu____3210 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3210
           then
             let uu____3211 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3212 =
               let uu____3213 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3213 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3211 uu____3212
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
        let uu____3245 =
          let uu____3252 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3252 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3245
          (FStar_Util.for_some
             (fun uu____3288  ->
                match uu____3288 with
                | (uv,uu____3294) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3301 'Auu____3302 .
    'Auu____3302 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3301)
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
            let uu____3334 = occurs wl uk t in Prims.op_Negation uu____3334 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3341 =
                 let uu____3342 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3343 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3342 uu____3343 in
               FStar_Pervasives_Native.Some uu____3341) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3353 'Auu____3354 .
    'Auu____3354 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3353)
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
            let uu____3408 = occurs_check env wl uk t in
            match uu____3408 with
            | (occurs_ok,msg) ->
                let uu____3439 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3439, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3462 'Auu____3463 .
    (FStar_Syntax_Syntax.bv,'Auu____3463) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3462) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3462) FStar_Pervasives_Native.tuple2
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
      let uu____3547 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3601  ->
                fun uu____3602  ->
                  match (uu____3601, uu____3602) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3683 =
                        let uu____3684 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3684 in
                      if uu____3683
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3709 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3709
                         then
                           let uu____3722 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3722)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3547 with | (isect,uu____3763) -> FStar_List.rev isect
let binders_eq:
  'Auu____3788 'Auu____3789 .
    (FStar_Syntax_Syntax.bv,'Auu____3789) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3788) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3844  ->
              fun uu____3845  ->
                match (uu____3844, uu____3845) with
                | ((a,uu____3863),(b,uu____3865)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3879 'Auu____3880 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3880) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3879)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3879)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____3931 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____3945  ->
                      match uu____3945 with
                      | (b,uu____3951) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____3931
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____3967 -> FStar_Pervasives_Native.None
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
            let uu____4040 = pat_var_opt env seen hd1 in
            (match uu____4040 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4054 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4054
                   then
                     let uu____4055 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4055
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4073 =
      let uu____4074 = FStar_Syntax_Subst.compress t in
      uu____4074.FStar_Syntax_Syntax.n in
    match uu____4073 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4077 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4094;
           FStar_Syntax_Syntax.pos = uu____4095;
           FStar_Syntax_Syntax.vars = uu____4096;_},uu____4097)
        -> true
    | uu____4134 -> false
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
           FStar_Syntax_Syntax.pos = uu____4258;
           FStar_Syntax_Syntax.vars = uu____4259;_},args)
        -> (t, uv, k, args)
    | uu____4327 -> failwith "Not a flex-uvar"
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
      let uu____4404 = destruct_flex_t t in
      match uu____4404 with
      | (t1,uv,k,args) ->
          let uu____4519 = pat_vars env [] args in
          (match uu____4519 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4617 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4698 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4733 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4737 -> false
let head_match: match_result -> match_result =
  fun uu___293_4740  ->
    match uu___293_4740 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4755 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4764 ->
          let uu____4765 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4765 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4776 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4795 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4804 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4831 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4832 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4833 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4850 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4863 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4887) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4893,uu____4894) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____4936) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____4957;
             FStar_Syntax_Syntax.index = uu____4958;
             FStar_Syntax_Syntax.sort = t2;_},uu____4960)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____4967 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____4968 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____4969 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____4982 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5000 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5000
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
            let uu____5021 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5021
            then FullMatch
            else
              (let uu____5023 =
                 let uu____5032 =
                   let uu____5035 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5035 in
                 let uu____5036 =
                   let uu____5039 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5039 in
                 (uu____5032, uu____5036) in
               MisMatch uu____5023)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5045),FStar_Syntax_Syntax.Tm_uinst (g,uu____5047)) ->
            let uu____5056 = head_matches env f g in
            FStar_All.pipe_right uu____5056 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5065),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5067)) ->
            let uu____5116 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5116
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5123),FStar_Syntax_Syntax.Tm_refine (y,uu____5125)) ->
            let uu____5134 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5134 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5136),uu____5137) ->
            let uu____5142 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5142 head_match
        | (uu____5143,FStar_Syntax_Syntax.Tm_refine (x,uu____5145)) ->
            let uu____5150 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5150 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5151,FStar_Syntax_Syntax.Tm_type
           uu____5152) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5153,FStar_Syntax_Syntax.Tm_arrow uu____5154) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5180),FStar_Syntax_Syntax.Tm_app (head',uu____5182))
            ->
            let uu____5223 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5223 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5225),uu____5226) ->
            let uu____5247 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5247 head_match
        | (uu____5248,FStar_Syntax_Syntax.Tm_app (head1,uu____5250)) ->
            let uu____5271 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5271 head_match
        | uu____5272 ->
            let uu____5277 =
              let uu____5286 = delta_depth_of_term env t11 in
              let uu____5289 = delta_depth_of_term env t21 in
              (uu____5286, uu____5289) in
            MisMatch uu____5277
let head_matches_delta:
  'Auu____5301 .
    FStar_TypeChecker_Env.env ->
      'Auu____5301 ->
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
            let uu____5334 = FStar_Syntax_Util.head_and_args t in
            match uu____5334 with
            | (head1,uu____5352) ->
                let uu____5373 =
                  let uu____5374 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5374.FStar_Syntax_Syntax.n in
                (match uu____5373 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5380 =
                       let uu____5381 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5381 FStar_Option.isSome in
                     if uu____5380
                     then
                       let uu____5400 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5400
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5404 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5507)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5525 =
                     let uu____5534 = maybe_inline t11 in
                     let uu____5537 = maybe_inline t21 in
                     (uu____5534, uu____5537) in
                   match uu____5525 with
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
                (uu____5574,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5592 =
                     let uu____5601 = maybe_inline t11 in
                     let uu____5604 = maybe_inline t21 in
                     (uu____5601, uu____5604) in
                   match uu____5592 with
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
                let uu____5647 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5647 with
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
                let uu____5670 =
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
                (match uu____5670 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5694 -> fail r
            | uu____5703 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5736 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____5772 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___294_5784  ->
    match uu___294_5784 with
    | T (t,uu____5786) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5802 = FStar_Syntax_Util.type_u () in
      match uu____5802 with
      | (t,uu____5808) ->
          let uu____5809 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____5809
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5820 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____5820 FStar_Pervasives_Native.fst
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
        let uu____5884 = head_matches env t1 t' in
        match uu____5884 with
        | MisMatch uu____5885 -> false
        | uu____5894 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____5990,imp),T (t2,uu____5993)) -> (t2, imp)
                     | uu____6012 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6079  ->
                    match uu____6079 with
                    | (t2,uu____6093) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6136 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6136 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6211))::tcs2) ->
                       aux
                         (((let uu___318_6246 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___318_6246.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___318_6246.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6264 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___295_6317 =
                 match uu___295_6317 with
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
               let uu____6434 = decompose1 [] bs1 in
               (rebuild, matches, uu____6434))
      | uu____6483 ->
          let rebuild uu___296_6489 =
            match uu___296_6489 with
            | [] -> t1
            | uu____6492 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___297_6523  ->
    match uu___297_6523 with
    | T (t,uu____6525) -> t
    | uu____6534 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___298_6537  ->
    match uu___298_6537 with
    | T (t,uu____6539) -> FStar_Syntax_Syntax.as_arg t
    | uu____6548 -> failwith "Impossible"
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
              | (uu____6654,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6679 = new_uvar r scope1 k in
                  (match uu____6679 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6697 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6714 =
                         let uu____6715 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6715 in
                       ((T (gi_xs, mk_kind)), uu____6714))
              | (uu____6728,uu____6729,C uu____6730) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____6877 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6894;
                         FStar_Syntax_Syntax.vars = uu____6895;_})
                        ->
                        let uu____6918 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6918 with
                         | (T (gi_xs,uu____6942),prob) ->
                             let uu____6952 =
                               let uu____6953 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____6953 in
                             (uu____6952, [prob])
                         | uu____6956 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6971;
                         FStar_Syntax_Syntax.vars = uu____6972;_})
                        ->
                        let uu____6995 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6995 with
                         | (T (gi_xs,uu____7019),prob) ->
                             let uu____7029 =
                               let uu____7030 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7030 in
                             (uu____7029, [prob])
                         | uu____7033 -> failwith "impossible")
                    | (uu____7044,uu____7045,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7047;
                         FStar_Syntax_Syntax.vars = uu____7048;_})
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
                        let uu____7179 =
                          let uu____7188 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7188 FStar_List.unzip in
                        (match uu____7179 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7242 =
                                 let uu____7243 =
                                   let uu____7246 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7246 un_T in
                                 let uu____7247 =
                                   let uu____7256 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7256
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7243;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7247;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7242 in
                             ((C gi_xs), sub_probs))
                    | uu____7265 ->
                        let uu____7278 = sub_prob scope1 args q in
                        (match uu____7278 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____6877 with
                   | (tc,probs) ->
                       let uu____7309 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7372,uu____7373),T
                            (t,uu____7375)) ->
                             let b1 =
                               ((let uu___319_7412 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___319_7412.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___319_7412.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7413 =
                               let uu____7420 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7420 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7413)
                         | uu____7455 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7309 with
                        | (bopt,scope2,args1) ->
                            let uu____7539 = aux scope2 args1 qs2 in
                            (match uu____7539 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7576 =
                                         let uu____7579 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7579 in
                                       FStar_Syntax_Util.mk_conj_l uu____7576
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7602 =
                                         let uu____7605 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7606 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7605 :: uu____7606 in
                                       FStar_Syntax_Util.mk_conj_l uu____7602 in
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
  'Auu____7674 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7674)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7674)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___320_7695 = p in
      let uu____7700 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7701 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___320_7695.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7700;
        FStar_TypeChecker_Common.relation =
          (uu___320_7695.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7701;
        FStar_TypeChecker_Common.element =
          (uu___320_7695.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___320_7695.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___320_7695.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___320_7695.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___320_7695.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___320_7695.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7713 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7713
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7722 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____7742 = compress_prob wl pr in
        FStar_All.pipe_right uu____7742 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7752 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____7752 with
           | (lh,uu____7772) ->
               let uu____7793 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____7793 with
                | (rh,uu____7813) ->
                    let uu____7834 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7851,FStar_Syntax_Syntax.Tm_uvar uu____7852)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7889,uu____7890)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____7911,FStar_Syntax_Syntax.Tm_uvar uu____7912)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7933,uu____7934)
                          ->
                          let uu____7951 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____7951 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8000 ->
                                    let rank =
                                      let uu____8008 = is_top_level_prob prob in
                                      if uu____8008
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8010 =
                                      let uu___321_8015 = tp in
                                      let uu____8020 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___321_8015.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___321_8015.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___321_8015.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8020;
                                        FStar_TypeChecker_Common.element =
                                          (uu___321_8015.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___321_8015.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___321_8015.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___321_8015.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___321_8015.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___321_8015.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8010)))
                      | (uu____8031,FStar_Syntax_Syntax.Tm_uvar uu____8032)
                          ->
                          let uu____8049 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8049 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8098 ->
                                    let uu____8105 =
                                      let uu___322_8112 = tp in
                                      let uu____8117 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___322_8112.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8117;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___322_8112.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___322_8112.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___322_8112.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___322_8112.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___322_8112.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___322_8112.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___322_8112.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___322_8112.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8105)))
                      | (uu____8134,uu____8135) -> (rigid_rigid, tp) in
                    (match uu____7834 with
                     | (rank,tp1) ->
                         let uu____8154 =
                           FStar_All.pipe_right
                             (let uu___323_8160 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___323_8160.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___323_8160.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___323_8160.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___323_8160.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___323_8160.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___323_8160.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___323_8160.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___323_8160.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___323_8160.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8154))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8170 =
            FStar_All.pipe_right
              (let uu___324_8176 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___324_8176.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___324_8176.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___324_8176.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___324_8176.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___324_8176.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___324_8176.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___324_8176.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___324_8176.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___324_8176.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8170)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8231 probs =
      match uu____8231 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8284 = rank wl hd1 in
               (match uu____8284 with
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
    match projectee with | UDeferred _0 -> true | uu____8391 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8403 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8415 -> false
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
                        let uu____8455 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8455 with
                        | (k,uu____8461) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8471 -> false)))
            | uu____8472 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8523 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8523 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8526 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8536 =
                     let uu____8537 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8538 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8537
                       uu____8538 in
                   UFailed uu____8536)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8558 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8558 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8580 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8580 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8583 ->
                let uu____8588 =
                  let uu____8589 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8590 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8589
                    uu____8590 msg in
                UFailed uu____8588 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8591,uu____8592) ->
              let uu____8593 =
                let uu____8594 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8595 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8594 uu____8595 in
              failwith uu____8593
          | (FStar_Syntax_Syntax.U_unknown ,uu____8596) ->
              let uu____8597 =
                let uu____8598 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8599 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8598 uu____8599 in
              failwith uu____8597
          | (uu____8600,FStar_Syntax_Syntax.U_bvar uu____8601) ->
              let uu____8602 =
                let uu____8603 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8604 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8603 uu____8604 in
              failwith uu____8602
          | (uu____8605,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8606 =
                let uu____8607 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8608 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8607 uu____8608 in
              failwith uu____8606
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8632 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8632
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8654 = occurs_univ v1 u3 in
              if uu____8654
              then
                let uu____8655 =
                  let uu____8656 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8657 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8656 uu____8657 in
                try_umax_components u11 u21 uu____8655
              else
                (let uu____8659 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8659)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8679 = occurs_univ v1 u3 in
              if uu____8679
              then
                let uu____8680 =
                  let uu____8681 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8682 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8681 uu____8682 in
                try_umax_components u11 u21 uu____8680
              else
                (let uu____8684 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8684)
          | (FStar_Syntax_Syntax.U_max uu____8693,uu____8694) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8700 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8700
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8702,FStar_Syntax_Syntax.U_max uu____8703) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8709 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8709
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8711,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8712,FStar_Syntax_Syntax.U_name
             uu____8713) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8714) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8715) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8716,FStar_Syntax_Syntax.U_succ
             uu____8717) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8718,FStar_Syntax_Syntax.U_zero
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
      let uu____8804 = bc1 in
      match uu____8804 with
      | (bs1,mk_cod1) ->
          let uu____8845 = bc2 in
          (match uu____8845 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____8915 = FStar_Util.first_N n1 bs in
                 match uu____8915 with
                 | (bs3,rest) ->
                     let uu____8940 = mk_cod rest in (bs3, uu____8940) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____8969 =
                   let uu____8976 = mk_cod1 [] in (bs1, uu____8976) in
                 let uu____8979 =
                   let uu____8986 = mk_cod2 [] in (bs2, uu____8986) in
                 (uu____8969, uu____8979)
               else
                 if l1 > l2
                 then
                   (let uu____9028 = curry l2 bs1 mk_cod1 in
                    let uu____9041 =
                      let uu____9048 = mk_cod2 [] in (bs2, uu____9048) in
                    (uu____9028, uu____9041))
                 else
                   (let uu____9064 =
                      let uu____9071 = mk_cod1 [] in (bs1, uu____9071) in
                    let uu____9074 = curry l1 bs2 mk_cod2 in
                    (uu____9064, uu____9074)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9195 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9195
       then
         let uu____9196 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9196
       else ());
      (let uu____9198 = next_prob probs in
       match uu____9198 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___325_9219 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___325_9219.wl_deferred);
               ctr = (uu___325_9219.ctr);
               defer_ok = (uu___325_9219.defer_ok);
               smt_ok = (uu___325_9219.smt_ok);
               tcenv = (uu___325_9219.tcenv)
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
                  let uu____9230 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9230 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9235 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9235 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9240,uu____9241) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9258 ->
                let uu____9267 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9326  ->
                          match uu____9326 with
                          | (c,uu____9334,uu____9335) -> c < probs.ctr)) in
                (match uu____9267 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9376 =
                            FStar_List.map
                              (fun uu____9391  ->
                                 match uu____9391 with
                                 | (uu____9402,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9376
                      | uu____9405 ->
                          let uu____9414 =
                            let uu___326_9415 = probs in
                            let uu____9416 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9437  ->
                                      match uu____9437 with
                                      | (uu____9444,uu____9445,y) -> y)) in
                            {
                              attempting = uu____9416;
                              wl_deferred = rest;
                              ctr = (uu___326_9415.ctr);
                              defer_ok = (uu___326_9415.defer_ok);
                              smt_ok = (uu___326_9415.smt_ok);
                              tcenv = (uu___326_9415.tcenv)
                            } in
                          solve env uu____9414))))
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
            let uu____9452 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9452 with
            | USolved wl1 ->
                let uu____9454 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9454
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
                  let uu____9500 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9500 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9503 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9515;
                  FStar_Syntax_Syntax.vars = uu____9516;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9519;
                  FStar_Syntax_Syntax.vars = uu____9520;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9534,uu____9535) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9542,FStar_Syntax_Syntax.Tm_uinst uu____9543) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9550 -> USolved wl
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
            ((let uu____9560 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9560
              then
                let uu____9561 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9561 msg
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
        (let uu____9570 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9570
         then
           let uu____9571 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9571
         else ());
        (let uu____9573 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9573 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9635 = head_matches_delta env () t1 t2 in
               match uu____9635 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9676 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____9725 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9740 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____9741 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____9740, uu____9741)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9746 = FStar_Syntax_Subst.compress t1 in
                              let uu____9747 = FStar_Syntax_Subst.compress t2 in
                              (uu____9746, uu____9747) in
                        (match uu____9725 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____9773 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____9773 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____9804 =
                                    let uu____9813 =
                                      let uu____9816 =
                                        let uu____9819 =
                                          let uu____9820 =
                                            let uu____9827 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____9827) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____9820 in
                                        FStar_Syntax_Syntax.mk uu____9819 in
                                      uu____9816 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____9835 =
                                      let uu____9838 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____9838] in
                                    (uu____9813, uu____9835) in
                                  FStar_Pervasives_Native.Some uu____9804
                              | (uu____9851,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9853)) ->
                                  let uu____9858 =
                                    let uu____9865 =
                                      let uu____9868 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____9868] in
                                    (t11, uu____9865) in
                                  FStar_Pervasives_Native.Some uu____9858
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9878),uu____9879) ->
                                  let uu____9884 =
                                    let uu____9891 =
                                      let uu____9894 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____9894] in
                                    (t21, uu____9891) in
                                  FStar_Pervasives_Native.Some uu____9884
                              | uu____9903 ->
                                  let uu____9908 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____9908 with
                                   | (head1,uu____9932) ->
                                       let uu____9953 =
                                         let uu____9954 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____9954.FStar_Syntax_Syntax.n in
                                       (match uu____9953 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____9965;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____9967;_}
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
                                        | uu____9974 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____9987) ->
                  let uu____10012 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___299_10038  ->
                            match uu___299_10038 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10045 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10045 with
                                      | (u',uu____10061) ->
                                          let uu____10082 =
                                            let uu____10083 = whnf env u' in
                                            uu____10083.FStar_Syntax_Syntax.n in
                                          (match uu____10082 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10087) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10112 -> false))
                                 | uu____10113 -> false)
                            | uu____10116 -> false)) in
                  (match uu____10012 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10150 tps =
                         match uu____10150 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10198 =
                                    let uu____10207 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10207 in
                                  (match uu____10198 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10242 -> FStar_Pervasives_Native.None) in
                       let uu____10251 =
                         let uu____10260 =
                           let uu____10267 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10267, []) in
                         make_lower_bound uu____10260 lower_bounds in
                       (match uu____10251 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10279 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10279
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
                            ((let uu____10299 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10299
                              then
                                let wl' =
                                  let uu___327_10301 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___327_10301.wl_deferred);
                                    ctr = (uu___327_10301.ctr);
                                    defer_ok = (uu___327_10301.defer_ok);
                                    smt_ok = (uu___327_10301.smt_ok);
                                    tcenv = (uu___327_10301.tcenv)
                                  } in
                                let uu____10302 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10302
                              else ());
                             (let uu____10304 =
                                solve_t env eq_prob
                                  (let uu___328_10306 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___328_10306.wl_deferred);
                                     ctr = (uu___328_10306.ctr);
                                     defer_ok = (uu___328_10306.defer_ok);
                                     smt_ok = (uu___328_10306.smt_ok);
                                     tcenv = (uu___328_10306.tcenv)
                                   }) in
                              match uu____10304 with
                              | Success uu____10309 ->
                                  let wl1 =
                                    let uu___329_10311 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___329_10311.wl_deferred);
                                      ctr = (uu___329_10311.ctr);
                                      defer_ok = (uu___329_10311.defer_ok);
                                      smt_ok = (uu___329_10311.smt_ok);
                                      tcenv = (uu___329_10311.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10313 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10318 -> FStar_Pervasives_Native.None))))
              | uu____10319 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10328 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10328
         then
           let uu____10329 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10329
         else ());
        (let uu____10331 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10331 with
         | (u,args) ->
             let uu____10370 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10370 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10411 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10411 with
                    | (h1,args1) ->
                        let uu____10452 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10452 with
                         | (h2,uu____10472) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10499 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10499
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10517 =
                                          let uu____10520 =
                                            let uu____10521 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10521 in
                                          [uu____10520] in
                                        FStar_Pervasives_Native.Some
                                          uu____10517))
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
                                       (let uu____10554 =
                                          let uu____10557 =
                                            let uu____10558 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10558 in
                                          [uu____10557] in
                                        FStar_Pervasives_Native.Some
                                          uu____10554))
                                  else FStar_Pervasives_Native.None
                              | uu____10572 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10662 =
                               let uu____10671 =
                                 let uu____10674 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10674 in
                               (uu____10671, m1) in
                             FStar_Pervasives_Native.Some uu____10662)
                    | (uu____10687,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10689)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____10737),uu____10738) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____10785 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10838) ->
                       let uu____10863 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___300_10889  ->
                                 match uu___300_10889 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____10896 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____10896 with
                                           | (u',uu____10912) ->
                                               let uu____10933 =
                                                 let uu____10934 =
                                                   whnf env u' in
                                                 uu____10934.FStar_Syntax_Syntax.n in
                                               (match uu____10933 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____10938) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____10963 -> false))
                                      | uu____10964 -> false)
                                 | uu____10967 -> false)) in
                       (match uu____10863 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11005 tps =
                              match uu____11005 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11067 =
                                         let uu____11078 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11078 in
                                       (match uu____11067 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11129 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11140 =
                              let uu____11151 =
                                let uu____11160 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11160, []) in
                              make_upper_bound uu____11151 upper_bounds in
                            (match uu____11140 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11174 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11174
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
                                 ((let uu____11200 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11200
                                   then
                                     let wl' =
                                       let uu___330_11202 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___330_11202.wl_deferred);
                                         ctr = (uu___330_11202.ctr);
                                         defer_ok = (uu___330_11202.defer_ok);
                                         smt_ok = (uu___330_11202.smt_ok);
                                         tcenv = (uu___330_11202.tcenv)
                                       } in
                                     let uu____11203 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11203
                                   else ());
                                  (let uu____11205 =
                                     solve_t env eq_prob
                                       (let uu___331_11207 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___331_11207.wl_deferred);
                                          ctr = (uu___331_11207.ctr);
                                          defer_ok =
                                            (uu___331_11207.defer_ok);
                                          smt_ok = (uu___331_11207.smt_ok);
                                          tcenv = (uu___331_11207.tcenv)
                                        }) in
                                   match uu____11205 with
                                   | Success uu____11210 ->
                                       let wl1 =
                                         let uu___332_11212 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___332_11212.wl_deferred);
                                           ctr = (uu___332_11212.ctr);
                                           defer_ok =
                                             (uu___332_11212.defer_ok);
                                           smt_ok = (uu___332_11212.smt_ok);
                                           tcenv = (uu___332_11212.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11214 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11219 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11220 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11295 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11295
                      then
                        let uu____11296 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11296
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___333_11350 = hd1 in
                      let uu____11351 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___333_11350.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___333_11350.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11351
                      } in
                    let hd21 =
                      let uu___334_11355 = hd2 in
                      let uu____11356 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___334_11355.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___334_11355.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11356
                      } in
                    let prob =
                      let uu____11360 =
                        let uu____11365 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11365 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11360 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11376 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11376 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11380 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11380 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11418 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11423 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11418 uu____11423 in
                         ((let uu____11433 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11433
                           then
                             let uu____11434 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11435 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11434 uu____11435
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11458 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11468 = aux scope env [] bs1 bs2 in
              match uu____11468 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11492 = compress_tprob wl problem in
        solve_t' env uu____11492 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11525 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11525 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11556,uu____11557) ->
                   let rec may_relate head3 =
                     let uu____11582 =
                       let uu____11583 = FStar_Syntax_Subst.compress head3 in
                       uu____11583.FStar_Syntax_Syntax.n in
                     match uu____11582 with
                     | FStar_Syntax_Syntax.Tm_name uu____11586 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11587 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11610;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11611;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11614;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11615;
                           FStar_Syntax_Syntax.fv_qual = uu____11616;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11620,uu____11621) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11663) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11669) ->
                         may_relate t
                     | uu____11674 -> false in
                   let uu____11675 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11675
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
                                let uu____11692 =
                                  let uu____11693 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11693 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11692 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11695 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11695
                   else
                     (let uu____11697 =
                        let uu____11698 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11699 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11698 uu____11699 in
                      giveup env1 uu____11697 orig)
               | (uu____11700,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___335_11714 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___335_11714.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___335_11714.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___335_11714.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___335_11714.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___335_11714.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___335_11714.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___335_11714.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___335_11714.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____11715,FStar_Pervasives_Native.None ) ->
                   ((let uu____11727 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____11727
                     then
                       let uu____11728 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11729 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____11730 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____11731 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____11728
                         uu____11729 uu____11730 uu____11731
                     else ());
                    (let uu____11733 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____11733 with
                     | (head11,args1) ->
                         let uu____11770 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____11770 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____11824 =
                                  let uu____11825 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____11826 = args_to_string args1 in
                                  let uu____11827 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____11828 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____11825 uu____11826 uu____11827
                                    uu____11828 in
                                giveup env1 uu____11824 orig
                              else
                                (let uu____11830 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____11836 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____11836 = FStar_Syntax_Util.Equal) in
                                 if uu____11830
                                 then
                                   let uu____11837 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____11837 with
                                   | USolved wl2 ->
                                       let uu____11839 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____11839
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____11843 =
                                      base_and_refinement env1 t1 in
                                    match uu____11843 with
                                    | (base1,refinement1) ->
                                        let uu____11868 =
                                          base_and_refinement env1 t2 in
                                        (match uu____11868 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____11925 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____11925 with
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
                                                           (fun uu____11947 
                                                              ->
                                                              fun uu____11948
                                                                 ->
                                                                match 
                                                                  (uu____11947,
                                                                    uu____11948)
                                                                with
                                                                | ((a,uu____11966),
                                                                   (a',uu____11968))
                                                                    ->
                                                                    let uu____11977
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
                                                                    uu____11977)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____11987 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____11987 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____11993 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___336_12029 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___336_12029.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12068 =
          match uu____12068 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12284  ->
                              match uu____12284 with
                              | (x,imp) ->
                                  let uu____12295 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12295, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12308 = FStar_Syntax_Util.type_u () in
                      match uu____12308 with
                      | (t1,uu____12314) ->
                          let uu____12315 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12315 in
                    let uu____12320 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12320 with
                     | (t',tm_u1) ->
                         let uu____12333 = destruct_flex_t t' in
                         (match uu____12333 with
                          | (uu____12370,u1,k1,uu____12373) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12432 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12432 in
                              let sol =
                                let uu____12436 =
                                  let uu____12445 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12445) in
                                TERM uu____12436 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____12581 = pat_var_opt env pat_args hd1 in
                    (match uu____12581 with
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
                                    (fun uu____12644  ->
                                       match uu____12644 with
                                       | (x,uu____12650) ->
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
                            let uu____12665 =
                              let uu____12666 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____12666 in
                            if uu____12665
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____12678 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____12678 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____12693::uu____12694) ->
                    let uu____12725 =
                      let uu____12738 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____12738 in
                    (match uu____12725 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____12777 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____12784::uu____12785,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____12820 =
                let uu____12833 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____12833 in
              (match uu____12820 with
               | (all_formals,res_t) ->
                   let uu____12858 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____12858 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____12892 = lhs in
          match uu____12892 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____12902 ->
                    let uu____12903 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____12903 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____12926 = p in
          match uu____12926 with
          | (((u,k),xs,c),ps,(h,uu____12937,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13019 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13019 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13042 = h gs_xs in
                     let uu____13043 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13042 uu____13043 in
                   ((let uu____13049 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13049
                     then
                       let uu____13050 =
                         let uu____13053 =
                           let uu____13054 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13054
                             (FStar_String.concat "\n\t") in
                         let uu____13059 =
                           let uu____13062 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13063 =
                             let uu____13066 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13067 =
                               let uu____13070 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13071 =
                                 let uu____13074 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13075 =
                                   let uu____13078 =
                                     let uu____13079 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13079
                                       (FStar_String.concat ", ") in
                                   let uu____13084 =
                                     let uu____13087 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13087] in
                                   uu____13078 :: uu____13084 in
                                 uu____13074 :: uu____13075 in
                               uu____13070 :: uu____13071 in
                             uu____13066 :: uu____13067 in
                           uu____13062 :: uu____13063 in
                         uu____13053 :: uu____13059 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13050
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___301_13108 =
          match uu___301_13108 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13140 = p in
          match uu____13140 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13231 = FStar_List.nth ps i in
              (match uu____13231 with
               | (pi,uu____13235) ->
                   let uu____13240 = FStar_List.nth xs i in
                   (match uu____13240 with
                    | (xi,uu____13252) ->
                        let rec gs k =
                          let uu____13265 =
                            let uu____13278 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13278 in
                          match uu____13265 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13353)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13366 = new_uvar r xs k_a in
                                    (match uu____13366 with
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
                                         let uu____13388 = aux subst2 tl1 in
                                         (match uu____13388 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13415 =
                                                let uu____13418 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13418 :: gi_xs' in
                                              let uu____13419 =
                                                let uu____13422 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13422 :: gi_ps' in
                                              (uu____13415, uu____13419))) in
                              aux [] bs in
                        let uu____13427 =
                          let uu____13428 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13428 in
                        if uu____13427
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13432 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13432 with
                           | (g_xs,uu____13444) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13455 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13456 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13455
                                   uu____13456 in
                               let sub1 =
                                 let uu____13462 =
                                   let uu____13467 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13470 =
                                     let uu____13473 =
                                       FStar_List.map
                                         (fun uu____13488  ->
                                            match uu____13488 with
                                            | (uu____13497,uu____13498,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13473 in
                                   mk_problem (p_scope orig) orig uu____13467
                                     (p_rel orig) uu____13470
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13462 in
                               ((let uu____13513 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13513
                                 then
                                   let uu____13514 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13515 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13514 uu____13515
                                 else ());
                                (let wl2 =
                                   let uu____13518 =
                                     let uu____13521 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13521 in
                                   solve_prob orig uu____13518
                                     [TERM (u, proj)] wl1 in
                                 let uu____13530 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13530))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13561 = lhs in
          match uu____13561 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13597 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13597 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13630 =
                        let uu____13677 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13677) in
                      FStar_Pervasives_Native.Some uu____13630
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____13821 =
                           let uu____13828 =
                             let uu____13829 = FStar_Syntax_Subst.compress k1 in
                             uu____13829.FStar_Syntax_Syntax.n in
                           (uu____13828, args) in
                         match uu____13821 with
                         | (uu____13840,[]) ->
                             let uu____13843 =
                               let uu____13854 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____13854) in
                             FStar_Pervasives_Native.Some uu____13843
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13875,uu____13876) ->
                             let uu____13897 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____13897 with
                              | (uv1,uv_args) ->
                                  let uu____13940 =
                                    let uu____13941 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13941.FStar_Syntax_Syntax.n in
                                  (match uu____13940 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13951) ->
                                       let uu____13976 =
                                         pat_vars env [] uv_args in
                                       (match uu____13976 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14003  ->
                                                      let uu____14004 =
                                                        let uu____14005 =
                                                          let uu____14006 =
                                                            let uu____14011 =
                                                              let uu____14012
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14012
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14011 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14006 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14005 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14004)) in
                                            let c1 =
                                              let uu____14022 =
                                                let uu____14023 =
                                                  let uu____14028 =
                                                    let uu____14029 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14029
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14028 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14023 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14022 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14042 =
                                                let uu____14045 =
                                                  let uu____14046 =
                                                    let uu____14049 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14049
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14046 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14045 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14042 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14067 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14072,uu____14073) ->
                             let uu____14092 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14092 with
                              | (uv1,uv_args) ->
                                  let uu____14135 =
                                    let uu____14136 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14136.FStar_Syntax_Syntax.n in
                                  (match uu____14135 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14146) ->
                                       let uu____14171 =
                                         pat_vars env [] uv_args in
                                       (match uu____14171 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14198  ->
                                                      let uu____14199 =
                                                        let uu____14200 =
                                                          let uu____14201 =
                                                            let uu____14206 =
                                                              let uu____14207
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14207
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14206 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14201 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14200 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14199)) in
                                            let c1 =
                                              let uu____14217 =
                                                let uu____14218 =
                                                  let uu____14223 =
                                                    let uu____14224 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14224
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14223 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14218 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14217 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14237 =
                                                let uu____14240 =
                                                  let uu____14241 =
                                                    let uu____14244 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14244
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14241 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14240 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14237 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14262 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14269) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14310 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14310
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14346 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14346 with
                                  | (args1,rest) ->
                                      let uu____14375 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14375 with
                                       | (xs2,c2) ->
                                           let uu____14388 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14388
                                             (fun uu____14412  ->
                                                match uu____14412 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14452 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14452 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14520 =
                                        let uu____14525 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14525 in
                                      FStar_All.pipe_right uu____14520
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14540 ->
                             let uu____14547 =
                               let uu____14548 =
                                 let uu____14553 =
                                   let uu____14554 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14555 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14556 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14554 uu____14555 uu____14556 in
                                 (uu____14553, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14548 in
                             FStar_Exn.raise uu____14547 in
                       let uu____14563 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14563
                         (fun uu____14618  ->
                            match uu____14618 with
                            | (xs1,c1) ->
                                let uu____14667 =
                                  let uu____14708 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____14708) in
                                FStar_Pervasives_Native.Some uu____14667)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____14829 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____14845 = project orig env wl1 i st in
                     match uu____14845 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____14859) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____14874 = imitate orig env wl1 st in
                  match uu____14874 with
                  | Failed uu____14879 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____14910 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____14910 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____14935 =
                      let uu____14936 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____14936 wl2 in
                    (match uu____14935 with
                     | Failed uu____14937 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____14955 = FStar_Syntax_Util.head_and_args t21 in
                match uu____14955 with
                | (hd1,uu____14971) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____14992 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15005 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15006 -> true
                     | uu____15023 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15027 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15027
                         then true
                         else
                           ((let uu____15030 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15030
                             then
                               let uu____15031 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15031
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15051 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15051 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15064 =
                            let uu____15065 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15065 in
                          giveup_or_defer1 orig uu____15064
                        else
                          (let uu____15067 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15067
                           then
                             let uu____15068 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15068
                              then
                                let uu____15069 = subterms args_lhs in
                                imitate' orig env wl1 uu____15069
                              else
                                ((let uu____15074 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15074
                                  then
                                    let uu____15075 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15076 = names_to_string fvs1 in
                                    let uu____15077 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15075 uu____15076 uu____15077
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
                               (let uu____15081 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15081
                                then
                                  ((let uu____15083 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15083
                                    then
                                      let uu____15084 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15085 = names_to_string fvs1 in
                                      let uu____15086 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15084 uu____15085 uu____15086
                                    else ());
                                   (let uu____15088 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15088))
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
                     (let uu____15099 =
                        let uu____15100 = FStar_Syntax_Free.names t1 in
                        check_head uu____15100 t2 in
                      if uu____15099
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15111 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15111
                          then
                            let uu____15112 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15113 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15112 uu____15113
                          else ());
                         (let uu____15121 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15121))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15198 uu____15199 r =
               match (uu____15198, uu____15199) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15397 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15397
                   then
                     let uu____15398 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15398
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15422 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15422
                       then
                         let uu____15423 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15424 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15425 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15426 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15427 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15423 uu____15424 uu____15425 uu____15426
                           uu____15427
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15487 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15487 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15501 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15501 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15555 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15555 in
                                  let uu____15558 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15558 k3)
                           else
                             (let uu____15562 =
                                let uu____15563 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15564 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15565 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15563 uu____15564 uu____15565 in
                              failwith uu____15562) in
                       let uu____15566 =
                         let uu____15573 =
                           let uu____15586 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15586 in
                         match uu____15573 with
                         | (bs,k1') ->
                             let uu____15611 =
                               let uu____15624 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15624 in
                             (match uu____15611 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15652 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15652 in
                                  let uu____15661 =
                                    let uu____15666 =
                                      let uu____15667 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15667.FStar_Syntax_Syntax.n in
                                    let uu____15670 =
                                      let uu____15671 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15671.FStar_Syntax_Syntax.n in
                                    (uu____15666, uu____15670) in
                                  (match uu____15661 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15680,uu____15681) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____15684,FStar_Syntax_Syntax.Tm_type
                                      uu____15685) -> (k2'_ys, [sub_prob])
                                   | uu____15688 ->
                                       let uu____15693 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15693 with
                                        | (t,uu____15705) ->
                                            let uu____15706 = new_uvar r zs t in
                                            (match uu____15706 with
                                             | (k_zs,uu____15718) ->
                                                 let kprob =
                                                   let uu____15720 =
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
                                                          _0_64) uu____15720 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15566 with
                       | (k_u',sub_probs) ->
                           let uu____15737 =
                             let uu____15748 =
                               let uu____15749 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15749 in
                             let uu____15758 =
                               let uu____15761 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15761 in
                             let uu____15764 =
                               let uu____15767 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15767 in
                             (uu____15748, uu____15758, uu____15764) in
                           (match uu____15737 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15786 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15786 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15805 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15805
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15809 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15809 with
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
             let solve_one_pat uu____15862 uu____15863 =
               match (uu____15862, uu____15863) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____15981 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____15981
                     then
                       let uu____15982 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____15983 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____15982 uu____15983
                     else ());
                    (let uu____15985 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____15985
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16004  ->
                              fun uu____16005  ->
                                match (uu____16004, uu____16005) with
                                | ((a,uu____16023),(t21,uu____16025)) ->
                                    let uu____16034 =
                                      let uu____16039 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16039
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16034
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16045 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16045 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16060 = occurs_check env wl (u1, k1) t21 in
                        match uu____16060 with
                        | (occurs_ok,uu____16068) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16076 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16076
                            then
                              let sol =
                                let uu____16078 =
                                  let uu____16087 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16087) in
                                TERM uu____16078 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16094 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16094
                               then
                                 let uu____16095 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16095 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16119,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16145 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16145
                                       then
                                         let uu____16146 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16146
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16153 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16155 = lhs in
             match uu____16155 with
             | (t1,u1,k1,args1) ->
                 let uu____16160 = rhs in
                 (match uu____16160 with
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
                       | uu____16200 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16210 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16210 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16228) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16235 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16235
                                    then
                                      let uu____16236 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16236
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16243 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16245 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16245
        then
          let uu____16246 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16246
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16250 = FStar_Util.physical_equality t1 t2 in
           if uu____16250
           then
             let uu____16251 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16251
           else
             ((let uu____16254 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16254
               then
                 let uu____16255 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16255
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16258,uu____16259) ->
                   let uu____16286 =
                     let uu___337_16287 = problem in
                     let uu____16288 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___337_16287.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16288;
                       FStar_TypeChecker_Common.relation =
                         (uu___337_16287.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___337_16287.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___337_16287.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___337_16287.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___337_16287.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___337_16287.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___337_16287.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___337_16287.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16286 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16289,uu____16290) ->
                   let uu____16297 =
                     let uu___337_16298 = problem in
                     let uu____16299 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___337_16298.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16299;
                       FStar_TypeChecker_Common.relation =
                         (uu___337_16298.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___337_16298.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___337_16298.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___337_16298.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___337_16298.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___337_16298.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___337_16298.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___337_16298.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16297 wl
               | (uu____16300,FStar_Syntax_Syntax.Tm_ascribed uu____16301) ->
                   let uu____16328 =
                     let uu___338_16329 = problem in
                     let uu____16330 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___338_16329.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___338_16329.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___338_16329.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16330;
                       FStar_TypeChecker_Common.element =
                         (uu___338_16329.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___338_16329.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___338_16329.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___338_16329.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___338_16329.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___338_16329.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16328 wl
               | (uu____16331,FStar_Syntax_Syntax.Tm_meta uu____16332) ->
                   let uu____16339 =
                     let uu___338_16340 = problem in
                     let uu____16341 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___338_16340.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___338_16340.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___338_16340.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16341;
                       FStar_TypeChecker_Common.element =
                         (uu___338_16340.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___338_16340.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___338_16340.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___338_16340.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___338_16340.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___338_16340.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16339 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16342,uu____16343) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16344,FStar_Syntax_Syntax.Tm_bvar uu____16345) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___302_16400 =
                     match uu___302_16400 with
                     | [] -> c
                     | bs ->
                         let uu____16422 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16422 in
                   let uu____16431 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16431 with
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
                                   let uu____16573 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16573
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16575 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16575))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___303_16651 =
                     match uu___303_16651 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16685 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16685 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16821 =
                                   let uu____16826 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16827 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16826
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16827 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16821))
               | (FStar_Syntax_Syntax.Tm_abs uu____16832,uu____16833) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____16858 -> true
                     | uu____16875 -> false in
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
                       (let uu____16922 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___339_16930 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___339_16930.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___339_16930.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___339_16930.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___339_16930.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___339_16930.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___339_16930.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___339_16930.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___339_16930.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___339_16930.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___339_16930.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___339_16930.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___339_16930.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___339_16930.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___339_16930.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___339_16930.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___339_16930.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___339_16930.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___339_16930.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___339_16930.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___339_16930.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___339_16930.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___339_16930.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___339_16930.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___339_16930.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___339_16930.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___339_16930.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___339_16930.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___339_16930.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___339_16930.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___339_16930.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___339_16930.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____16922 with
                        | (uu____16933,ty,uu____16935) ->
                            let uu____16936 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____16936) in
                   let uu____16937 =
                     let uu____16954 = maybe_eta t1 in
                     let uu____16961 = maybe_eta t2 in
                     (uu____16954, uu____16961) in
                   (match uu____16937 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___340_17003 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___340_17003.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___340_17003.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___340_17003.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___340_17003.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___340_17003.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___340_17003.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___340_17003.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___340_17003.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17026 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17026
                        then
                          let uu____17027 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17027 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17042 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17042.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17042.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17042.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17042.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17042.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17042.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17042.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17042.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17066 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17066
                        then
                          let uu____17067 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17067 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17082 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17082.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17082.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17082.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17082.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17082.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17082.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17082.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17082.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17086 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17103,FStar_Syntax_Syntax.Tm_abs uu____17104) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17129 -> true
                     | uu____17146 -> false in
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
                       (let uu____17193 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___339_17201 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___339_17201.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___339_17201.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___339_17201.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___339_17201.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___339_17201.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___339_17201.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___339_17201.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___339_17201.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___339_17201.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___339_17201.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___339_17201.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___339_17201.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___339_17201.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___339_17201.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___339_17201.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___339_17201.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___339_17201.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___339_17201.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___339_17201.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___339_17201.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___339_17201.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___339_17201.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___339_17201.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___339_17201.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___339_17201.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___339_17201.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___339_17201.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___339_17201.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___339_17201.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___339_17201.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___339_17201.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17193 with
                        | (uu____17204,ty,uu____17206) ->
                            let uu____17207 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17207) in
                   let uu____17208 =
                     let uu____17225 = maybe_eta t1 in
                     let uu____17232 = maybe_eta t2 in
                     (uu____17225, uu____17232) in
                   (match uu____17208 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___340_17274 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___340_17274.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___340_17274.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___340_17274.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___340_17274.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___340_17274.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___340_17274.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___340_17274.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___340_17274.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17297 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17297
                        then
                          let uu____17298 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17298 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17313 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17313.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17313.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17313.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17313.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17313.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17313.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17313.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17313.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17337 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17337
                        then
                          let uu____17338 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17338 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17353 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17353.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17353.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17353.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17353.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17353.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17353.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17353.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17353.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17357 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17374,FStar_Syntax_Syntax.Tm_refine uu____17375) ->
                   let uu____17388 = as_refinement env wl t1 in
                   (match uu____17388 with
                    | (x1,phi1) ->
                        let uu____17395 = as_refinement env wl t2 in
                        (match uu____17395 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17403 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17403 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17441 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17441
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17445 =
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
                                 let uu____17451 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17451 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17460 =
                                   let uu____17465 =
                                     let uu____17466 =
                                       let uu____17473 =
                                         FStar_Syntax_Syntax.mk_binder x11 in
                                       [uu____17473] in
                                     FStar_List.append (p_scope orig)
                                       uu____17466 in
                                   mk_problem uu____17465 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17460 in
                               let uu____17482 =
                                 solve env1
                                   (let uu___342_17484 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___342_17484.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___342_17484.smt_ok);
                                      tcenv = (uu___342_17484.tcenv)
                                    }) in
                               (match uu____17482 with
                                | Failed uu____17491 -> fallback ()
                                | Success uu____17496 ->
                                    let guard =
                                      let uu____17500 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17505 =
                                        let uu____17506 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17506
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17500
                                        uu____17505 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___343_17515 = wl1 in
                                      {
                                        attempting =
                                          (uu___343_17515.attempting);
                                        wl_deferred =
                                          (uu___343_17515.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___343_17515.defer_ok);
                                        smt_ok = (uu___343_17515.smt_ok);
                                        tcenv = (uu___343_17515.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17517,FStar_Syntax_Syntax.Tm_uvar uu____17518) ->
                   let uu____17551 = destruct_flex_t t1 in
                   let uu____17552 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17551 uu____17552
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17553;
                     FStar_Syntax_Syntax.pos = uu____17554;
                     FStar_Syntax_Syntax.vars = uu____17555;_},uu____17556),FStar_Syntax_Syntax.Tm_uvar
                  uu____17557) ->
                   let uu____17610 = destruct_flex_t t1 in
                   let uu____17611 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17610 uu____17611
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17612,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17613;
                     FStar_Syntax_Syntax.pos = uu____17614;
                     FStar_Syntax_Syntax.vars = uu____17615;_},uu____17616))
                   ->
                   let uu____17669 = destruct_flex_t t1 in
                   let uu____17670 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17669 uu____17670
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17671;
                     FStar_Syntax_Syntax.pos = uu____17672;
                     FStar_Syntax_Syntax.vars = uu____17673;_},uu____17674),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17675;
                     FStar_Syntax_Syntax.pos = uu____17676;
                     FStar_Syntax_Syntax.vars = uu____17677;_},uu____17678))
                   ->
                   let uu____17751 = destruct_flex_t t1 in
                   let uu____17752 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17751 uu____17752
               | (FStar_Syntax_Syntax.Tm_uvar uu____17753,uu____17754) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17771 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17771 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17778;
                     FStar_Syntax_Syntax.pos = uu____17779;
                     FStar_Syntax_Syntax.vars = uu____17780;_},uu____17781),uu____17782)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17819 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17819 t2 wl
               | (uu____17826,FStar_Syntax_Syntax.Tm_uvar uu____17827) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____17844,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17845;
                     FStar_Syntax_Syntax.pos = uu____17846;
                     FStar_Syntax_Syntax.vars = uu____17847;_},uu____17848))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17885,FStar_Syntax_Syntax.Tm_type uu____17886) ->
                   solve_t' env
                     (let uu___344_17904 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_17904.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_17904.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_17904.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_17904.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_17904.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_17904.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_17904.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_17904.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_17904.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17905;
                     FStar_Syntax_Syntax.pos = uu____17906;
                     FStar_Syntax_Syntax.vars = uu____17907;_},uu____17908),FStar_Syntax_Syntax.Tm_type
                  uu____17909) ->
                   solve_t' env
                     (let uu___344_17947 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_17947.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_17947.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_17947.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_17947.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_17947.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_17947.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_17947.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_17947.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_17947.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17948,FStar_Syntax_Syntax.Tm_arrow uu____17949) ->
                   solve_t' env
                     (let uu___344_17979 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_17979.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_17979.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_17979.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_17979.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_17979.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_17979.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_17979.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_17979.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_17979.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17980;
                     FStar_Syntax_Syntax.pos = uu____17981;
                     FStar_Syntax_Syntax.vars = uu____17982;_},uu____17983),FStar_Syntax_Syntax.Tm_arrow
                  uu____17984) ->
                   solve_t' env
                     (let uu___344_18034 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_18034.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_18034.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_18034.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_18034.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_18034.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_18034.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_18034.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_18034.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_18034.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18035,uu____18036) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18055 =
                        let uu____18056 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18056 in
                      if uu____18055
                      then
                        let uu____18057 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___345_18063 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___345_18063.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___345_18063.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___345_18063.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___345_18063.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___345_18063.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___345_18063.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___345_18063.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___345_18063.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___345_18063.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18064 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18057 uu____18064 t2
                          wl
                      else
                        (let uu____18072 = base_and_refinement env t2 in
                         match uu____18072 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18101 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___346_18107 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___346_18107.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___346_18107.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___346_18107.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___346_18107.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___346_18107.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___346_18107.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___346_18107.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___346_18107.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___346_18107.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18108 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18101
                                    uu____18108 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___347_18122 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___347_18122.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___347_18122.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18125 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18125 in
                                  let guard =
                                    let uu____18137 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18137
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18145;
                     FStar_Syntax_Syntax.pos = uu____18146;
                     FStar_Syntax_Syntax.vars = uu____18147;_},uu____18148),uu____18149)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18188 =
                        let uu____18189 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18189 in
                      if uu____18188
                      then
                        let uu____18190 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___345_18196 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___345_18196.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___345_18196.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___345_18196.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___345_18196.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___345_18196.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___345_18196.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___345_18196.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___345_18196.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___345_18196.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18197 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18190 uu____18197 t2
                          wl
                      else
                        (let uu____18205 = base_and_refinement env t2 in
                         match uu____18205 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18234 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___346_18240 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___346_18240.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___346_18240.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___346_18240.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___346_18240.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___346_18240.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___346_18240.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___346_18240.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___346_18240.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___346_18240.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18241 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18234
                                    uu____18241 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___347_18255 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___347_18255.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___347_18255.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18258 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18258 in
                                  let guard =
                                    let uu____18270 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18270
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18278,FStar_Syntax_Syntax.Tm_uvar uu____18279) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18297 = base_and_refinement env t1 in
                      match uu____18297 with
                      | (t_base,uu____18309) ->
                          solve_t env
                            (let uu___348_18323 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___348_18323.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___348_18323.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___348_18323.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___348_18323.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___348_18323.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___348_18323.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___348_18323.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___348_18323.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18324,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18325;
                     FStar_Syntax_Syntax.pos = uu____18326;
                     FStar_Syntax_Syntax.vars = uu____18327;_},uu____18328))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18366 = base_and_refinement env t1 in
                      match uu____18366 with
                      | (t_base,uu____18378) ->
                          solve_t env
                            (let uu___348_18392 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___348_18392.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___348_18392.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___348_18392.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___348_18392.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___348_18392.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___348_18392.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___348_18392.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___348_18392.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18393,uu____18394) ->
                   let t21 =
                     let uu____18404 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18404 in
                   solve_t env
                     (let uu___349_18428 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___349_18428.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___349_18428.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___349_18428.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___349_18428.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___349_18428.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___349_18428.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___349_18428.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___349_18428.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___349_18428.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18429,FStar_Syntax_Syntax.Tm_refine uu____18430) ->
                   let t11 =
                     let uu____18440 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18440 in
                   solve_t env
                     (let uu___350_18464 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___350_18464.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___350_18464.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___350_18464.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___350_18464.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___350_18464.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___350_18464.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___350_18464.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___350_18464.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___350_18464.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18467,uu____18468) ->
                   let head1 =
                     let uu____18494 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18494
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18538 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18538
                       FStar_Pervasives_Native.fst in
                   let uu____18579 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18579
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18594 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18594
                      then
                        let guard =
                          let uu____18606 =
                            let uu____18607 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18607 = FStar_Syntax_Util.Equal in
                          if uu____18606
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18611 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18611) in
                        let uu____18614 = solve_prob orig guard [] wl in
                        solve env uu____18614
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18617,uu____18618) ->
                   let head1 =
                     let uu____18628 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18628
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18672 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18672
                       FStar_Pervasives_Native.fst in
                   let uu____18713 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18713
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18728 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18728
                      then
                        let guard =
                          let uu____18740 =
                            let uu____18741 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18741 = FStar_Syntax_Util.Equal in
                          if uu____18740
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18745 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18745) in
                        let uu____18748 = solve_prob orig guard [] wl in
                        solve env uu____18748
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18751,uu____18752) ->
                   let head1 =
                     let uu____18756 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18756
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18800 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18800
                       FStar_Pervasives_Native.fst in
                   let uu____18841 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18841
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18856 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18856
                      then
                        let guard =
                          let uu____18868 =
                            let uu____18869 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18869 = FStar_Syntax_Util.Equal in
                          if uu____18868
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18873 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____18873) in
                        let uu____18876 = solve_prob orig guard [] wl in
                        solve env uu____18876
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____18879,uu____18880) ->
                   let head1 =
                     let uu____18884 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18884
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18928 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18928
                       FStar_Pervasives_Native.fst in
                   let uu____18969 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18969
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18984 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18984
                      then
                        let guard =
                          let uu____18996 =
                            let uu____18997 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18997 = FStar_Syntax_Util.Equal in
                          if uu____18996
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19001 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19001) in
                        let uu____19004 = solve_prob orig guard [] wl in
                        solve env uu____19004
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19007,uu____19008) ->
                   let head1 =
                     let uu____19012 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19012
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19056 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19056
                       FStar_Pervasives_Native.fst in
                   let uu____19097 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19097
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19112 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19112
                      then
                        let guard =
                          let uu____19124 =
                            let uu____19125 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19125 = FStar_Syntax_Util.Equal in
                          if uu____19124
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19129 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19129) in
                        let uu____19132 = solve_prob orig guard [] wl in
                        solve env uu____19132
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19135,uu____19136) ->
                   let head1 =
                     let uu____19154 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19154
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19198 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19198
                       FStar_Pervasives_Native.fst in
                   let uu____19239 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19239
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19254 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19254
                      then
                        let guard =
                          let uu____19266 =
                            let uu____19267 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19267 = FStar_Syntax_Util.Equal in
                          if uu____19266
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19271 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19271) in
                        let uu____19274 = solve_prob orig guard [] wl in
                        solve env uu____19274
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19277,FStar_Syntax_Syntax.Tm_match uu____19278) ->
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
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19421) in
                        let uu____19424 = solve_prob orig guard [] wl in
                        solve env uu____19424
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19427,FStar_Syntax_Syntax.Tm_uinst uu____19428) ->
                   let head1 =
                     let uu____19438 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19438
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19482 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19482
                       FStar_Pervasives_Native.fst in
                   let uu____19523 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19523
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19538 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19538
                      then
                        let guard =
                          let uu____19550 =
                            let uu____19551 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19551 = FStar_Syntax_Util.Equal in
                          if uu____19550
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19555 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19555) in
                        let uu____19558 = solve_prob orig guard [] wl in
                        solve env uu____19558
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19561,FStar_Syntax_Syntax.Tm_name uu____19562) ->
                   let head1 =
                     let uu____19566 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19566
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19610 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19610
                       FStar_Pervasives_Native.fst in
                   let uu____19651 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19651
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19666 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19666
                      then
                        let guard =
                          let uu____19678 =
                            let uu____19679 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19679 = FStar_Syntax_Util.Equal in
                          if uu____19678
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19683 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19683) in
                        let uu____19686 = solve_prob orig guard [] wl in
                        solve env uu____19686
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19689,FStar_Syntax_Syntax.Tm_constant uu____19690) ->
                   let head1 =
                     let uu____19694 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19694
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19738 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19738
                       FStar_Pervasives_Native.fst in
                   let uu____19779 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19779
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19794 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19794
                      then
                        let guard =
                          let uu____19806 =
                            let uu____19807 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19807 = FStar_Syntax_Util.Equal in
                          if uu____19806
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19811 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19811) in
                        let uu____19814 = solve_prob orig guard [] wl in
                        solve env uu____19814
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19817,FStar_Syntax_Syntax.Tm_fvar uu____19818) ->
                   let head1 =
                     let uu____19822 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19822
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19866 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19866
                       FStar_Pervasives_Native.fst in
                   let uu____19907 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19907
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19922 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19922
                      then
                        let guard =
                          let uu____19934 =
                            let uu____19935 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19935 = FStar_Syntax_Util.Equal in
                          if uu____19934
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19939 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____19939) in
                        let uu____19942 = solve_prob orig guard [] wl in
                        solve env uu____19942
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19945,FStar_Syntax_Syntax.Tm_app uu____19946) ->
                   let head1 =
                     let uu____19964 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19964
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20008 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20008
                       FStar_Pervasives_Native.fst in
                   let uu____20049 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20049
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20064 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20064
                      then
                        let guard =
                          let uu____20076 =
                            let uu____20077 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20077 = FStar_Syntax_Util.Equal in
                          if uu____20076
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20081 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20081) in
                        let uu____20084 = solve_prob orig guard [] wl in
                        solve env uu____20084
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20087,uu____20088) ->
                   let uu____20101 =
                     let uu____20102 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20103 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20102
                       uu____20103 in
                   failwith uu____20101
               | (FStar_Syntax_Syntax.Tm_delayed uu____20104,uu____20105) ->
                   let uu____20130 =
                     let uu____20131 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20132 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20131
                       uu____20132 in
                   failwith uu____20130
               | (uu____20133,FStar_Syntax_Syntax.Tm_delayed uu____20134) ->
                   let uu____20159 =
                     let uu____20160 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20161 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20160
                       uu____20161 in
                   failwith uu____20159
               | (uu____20162,FStar_Syntax_Syntax.Tm_let uu____20163) ->
                   let uu____20176 =
                     let uu____20177 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20178 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20177
                       uu____20178 in
                   failwith uu____20176
               | uu____20179 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20215 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20215
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20217 =
               let uu____20218 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20219 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20218 uu____20219 in
             giveup env uu____20217 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20239  ->
                    fun uu____20240  ->
                      match (uu____20239, uu____20240) with
                      | ((a1,uu____20258),(a2,uu____20260)) ->
                          let uu____20269 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20269)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20279 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20279 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20303 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20310)::[] -> wp1
              | uu____20327 ->
                  let uu____20336 =
                    let uu____20337 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20337 in
                  failwith uu____20336 in
            let uu____20340 =
              let uu____20349 =
                let uu____20350 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20350 in
              [uu____20349] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20340;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20351 = lift_c1 () in solve_eq uu____20351 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___304_20357  ->
                       match uu___304_20357 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20358 -> false)) in
             let uu____20359 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20393)::uu____20394,(wp2,uu____20396)::uu____20397)
                   -> (wp1, wp2)
               | uu____20454 ->
                   let uu____20475 =
                     let uu____20476 =
                       let uu____20481 =
                         let uu____20482 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20483 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20482 uu____20483 in
                       (uu____20481, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20476 in
                   FStar_Exn.raise uu____20475 in
             match uu____20359 with
             | (wpc1,wpc2) ->
                 let uu____20502 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20502
                 then
                   let uu____20505 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20505 wl
                 else
                   (let uu____20509 =
                      let uu____20516 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20516 in
                    match uu____20509 with
                    | (c2_decl,qualifiers) ->
                        let uu____20537 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20537
                        then
                          let c1_repr =
                            let uu____20541 =
                              let uu____20542 =
                                let uu____20543 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20543 in
                              let uu____20544 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20542 uu____20544 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20541 in
                          let c2_repr =
                            let uu____20546 =
                              let uu____20547 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20548 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20547 uu____20548 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20546 in
                          let prob =
                            let uu____20550 =
                              let uu____20555 =
                                let uu____20556 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20557 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20556
                                  uu____20557 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20555 in
                            FStar_TypeChecker_Common.TProb uu____20550 in
                          let wl1 =
                            let uu____20559 =
                              let uu____20562 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20562 in
                            solve_prob orig uu____20559 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20571 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20571
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____20573 =
                                     let uu____20576 =
                                       let uu____20577 =
                                         let uu____20592 =
                                           let uu____20593 =
                                             let uu____20594 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____20594] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____20593 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20595 =
                                           let uu____20598 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20599 =
                                             let uu____20602 =
                                               let uu____20603 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20603 in
                                             [uu____20602] in
                                           uu____20598 :: uu____20599 in
                                         (uu____20592, uu____20595) in
                                       FStar_Syntax_Syntax.Tm_app uu____20577 in
                                     FStar_Syntax_Syntax.mk uu____20576 in
                                   uu____20573 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____20610 =
                                    let uu____20613 =
                                      let uu____20614 =
                                        let uu____20629 =
                                          let uu____20630 =
                                            let uu____20631 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____20631] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____20630 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20632 =
                                          let uu____20635 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20636 =
                                            let uu____20639 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20640 =
                                              let uu____20643 =
                                                let uu____20644 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20644 in
                                              [uu____20643] in
                                            uu____20639 :: uu____20640 in
                                          uu____20635 :: uu____20636 in
                                        (uu____20629, uu____20632) in
                                      FStar_Syntax_Syntax.Tm_app uu____20614 in
                                    FStar_Syntax_Syntax.mk uu____20613 in
                                  uu____20610 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20651 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20651 in
                           let wl1 =
                             let uu____20661 =
                               let uu____20664 =
                                 let uu____20667 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20667 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20664 in
                             solve_prob orig uu____20661 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20680 = FStar_Util.physical_equality c1 c2 in
        if uu____20680
        then
          let uu____20681 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20681
        else
          ((let uu____20684 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20684
            then
              let uu____20685 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20686 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20685
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20686
            else ());
           (let uu____20688 =
              let uu____20693 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20694 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20693, uu____20694) in
            match uu____20688 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20698),FStar_Syntax_Syntax.Total
                    (t2,uu____20700)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20717 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20717 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20720,FStar_Syntax_Syntax.Total uu____20721) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20739),FStar_Syntax_Syntax.Total
                    (t2,uu____20741)) ->
                     let uu____20758 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20758 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20762),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20764)) ->
                     let uu____20781 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20781 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20785),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20787)) ->
                     let uu____20804 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20804 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20807,FStar_Syntax_Syntax.Comp uu____20808) ->
                     let uu____20817 =
                       let uu___351_20822 = problem in
                       let uu____20827 =
                         let uu____20828 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20828 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___351_20822.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20827;
                         FStar_TypeChecker_Common.relation =
                           (uu___351_20822.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___351_20822.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___351_20822.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___351_20822.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___351_20822.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___351_20822.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___351_20822.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___351_20822.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20817 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20829,FStar_Syntax_Syntax.Comp uu____20830) ->
                     let uu____20839 =
                       let uu___351_20844 = problem in
                       let uu____20849 =
                         let uu____20850 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20850 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___351_20844.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20849;
                         FStar_TypeChecker_Common.relation =
                           (uu___351_20844.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___351_20844.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___351_20844.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___351_20844.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___351_20844.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___351_20844.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___351_20844.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___351_20844.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20839 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20851,FStar_Syntax_Syntax.GTotal uu____20852) ->
                     let uu____20861 =
                       let uu___352_20866 = problem in
                       let uu____20871 =
                         let uu____20872 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20872 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___352_20866.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___352_20866.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___352_20866.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20871;
                         FStar_TypeChecker_Common.element =
                           (uu___352_20866.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___352_20866.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___352_20866.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___352_20866.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___352_20866.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___352_20866.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20861 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20873,FStar_Syntax_Syntax.Total uu____20874) ->
                     let uu____20883 =
                       let uu___352_20888 = problem in
                       let uu____20893 =
                         let uu____20894 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20894 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___352_20888.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___352_20888.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___352_20888.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20893;
                         FStar_TypeChecker_Common.element =
                           (uu___352_20888.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___352_20888.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___352_20888.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___352_20888.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___352_20888.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___352_20888.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20883 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20895,FStar_Syntax_Syntax.Comp uu____20896) ->
                     let uu____20897 =
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
                     if uu____20897
                     then
                       let uu____20898 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____20898 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20904 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20914 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____20915 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____20914, uu____20915)) in
                          match uu____20904 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____20922 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____20922
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20924 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____20924 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20927 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____20929 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____20929) in
                                if uu____20927
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
                                  (let uu____20932 =
                                     let uu____20933 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____20934 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____20933 uu____20934 in
                                   giveup env uu____20932 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____20939 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20977  ->
              match uu____20977 with
              | (uu____20990,uu____20991,u,uu____20993,uu____20994,uu____20995)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____20939 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21026 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21026 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21044 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21072  ->
                match uu____21072 with
                | (u1,u2) ->
                    let uu____21079 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21080 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21079 uu____21080)) in
      FStar_All.pipe_right uu____21044 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21097,[])) -> "{}"
      | uu____21122 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21139 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21139
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21142 =
              FStar_List.map
                (fun uu____21152  ->
                   match uu____21152 with
                   | (uu____21157,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21142 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21162 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21162 imps
let new_t_problem:
  'Auu____21170 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21170 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21170)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21204 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21204
                then
                  let uu____21205 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21206 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21205
                    (rel_to_string rel) uu____21206
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
            let uu____21230 =
              let uu____21233 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21233 in
            FStar_Syntax_Syntax.new_bv uu____21230 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21242 =
              let uu____21245 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21245 in
            let uu____21248 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21242 uu____21248 in
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
          let uu____21278 = FStar_Options.eager_inference () in
          if uu____21278
          then
            let uu___353_21279 = probs in
            {
              attempting = (uu___353_21279.attempting);
              wl_deferred = (uu___353_21279.wl_deferred);
              ctr = (uu___353_21279.ctr);
              defer_ok = false;
              smt_ok = (uu___353_21279.smt_ok);
              tcenv = (uu___353_21279.tcenv)
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
             (let uu____21291 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21291
              then
                let uu____21292 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21292
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
          ((let uu____21302 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21302
            then
              let uu____21303 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21303
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21307 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21307
             then
               let uu____21308 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21308
             else ());
            (let f2 =
               let uu____21311 =
                 let uu____21312 = FStar_Syntax_Util.unmeta f1 in
                 uu____21312.FStar_Syntax_Syntax.n in
               match uu____21311 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21316 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___354_21317 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___354_21317.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___354_21317.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___354_21317.FStar_TypeChecker_Env.implicits)
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
            let uu____21336 =
              let uu____21337 =
                let uu____21338 =
                  let uu____21339 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21339
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21338;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21337 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21336
let with_guard_no_simp:
  'Auu____21366 .
    'Auu____21366 ->
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
            let uu____21386 =
              let uu____21387 =
                let uu____21388 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21388
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21387;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21386
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
          (let uu____21426 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21426
           then
             let uu____21427 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21428 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21427
               uu____21428
           else ());
          (let prob =
             let uu____21431 =
               let uu____21436 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21436 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21431 in
           let g =
             let uu____21444 =
               let uu____21447 = singleton' env prob smt_ok in
               solve_and_commit env uu____21447
                 (fun uu____21449  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21444 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21467 = try_teq true env t1 t2 in
        match uu____21467 with
        | FStar_Pervasives_Native.None  ->
            let uu____21470 =
              let uu____21471 =
                let uu____21476 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21477 = FStar_TypeChecker_Env.get_range env in
                (uu____21476, uu____21477) in
              FStar_Errors.Error uu____21471 in
            FStar_Exn.raise uu____21470
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21480 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21480
              then
                let uu____21481 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21482 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21483 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21481
                  uu____21482 uu____21483
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
          (let uu____21500 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21500
           then
             let uu____21501 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21502 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21501
               uu____21502
           else ());
          (let uu____21504 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21504 with
           | (prob,x) ->
               let g =
                 let uu____21516 =
                   let uu____21519 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21519
                     (fun uu____21521  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21516 in
               ((let uu____21531 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____21531
                 then
                   let uu____21532 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____21533 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____21534 =
                     let uu____21535 = FStar_Util.must g in
                     guard_to_string env uu____21535 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____21532 uu____21533 uu____21534
                 else ());
                (let uu____21537 =
                   let uu____21540 = FStar_Syntax_Syntax.mk_binder x in
                   abstract_guard uu____21540 in
                 FStar_Util.map_opt g uu____21537)))
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
          let uu____21564 = FStar_TypeChecker_Env.get_range env in
          let uu____21565 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21564 uu____21565
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21578 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21578
         then
           let uu____21579 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21580 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21579
             uu____21580
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21585 =
             let uu____21590 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21590 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21585 in
         let uu____21595 =
           let uu____21598 = singleton env prob in
           solve_and_commit env uu____21598
             (fun uu____21600  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21595)
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
      fun uu____21629  ->
        match uu____21629 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21668 =
                 let uu____21669 =
                   let uu____21674 =
                     let uu____21675 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21676 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21675 uu____21676 in
                   let uu____21677 = FStar_TypeChecker_Env.get_range env in
                   (uu____21674, uu____21677) in
                 FStar_Errors.Error uu____21669 in
               FStar_Exn.raise uu____21668) in
            let equiv1 v1 v' =
              let uu____21685 =
                let uu____21690 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21691 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21690, uu____21691) in
              match uu____21685 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21710 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21740 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21740 with
                      | FStar_Syntax_Syntax.U_unif uu____21747 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21776  ->
                                    match uu____21776 with
                                    | (u,v') ->
                                        let uu____21785 = equiv1 v1 v' in
                                        if uu____21785
                                        then
                                          let uu____21788 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21788 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21804 -> [])) in
            let uu____21809 =
              let wl =
                let uu___355_21813 = empty_worklist env in
                {
                  attempting = (uu___355_21813.attempting);
                  wl_deferred = (uu___355_21813.wl_deferred);
                  ctr = (uu___355_21813.ctr);
                  defer_ok = false;
                  smt_ok = (uu___355_21813.smt_ok);
                  tcenv = (uu___355_21813.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21831  ->
                      match uu____21831 with
                      | (lb,v1) ->
                          let uu____21838 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21838 with
                           | USolved wl1 -> ()
                           | uu____21840 -> fail lb v1))) in
            let rec check_ineq uu____21848 =
              match uu____21848 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21857) -> true
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
                      uu____21880,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21882,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21893) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21900,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21908 -> false) in
            let uu____21913 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21928  ->
                      match uu____21928 with
                      | (u,v1) ->
                          let uu____21935 = check_ineq (u, v1) in
                          if uu____21935
                          then true
                          else
                            ((let uu____21938 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____21938
                              then
                                let uu____21939 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____21940 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____21939
                                  uu____21940
                              else ());
                             false))) in
            if uu____21913
            then ()
            else
              ((let uu____21944 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____21944
                then
                  ((let uu____21946 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21946);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21956 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21956))
                else ());
               (let uu____21966 =
                  let uu____21967 =
                    let uu____21972 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____21972) in
                  FStar_Errors.Error uu____21967 in
                FStar_Exn.raise uu____21966))
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
      let fail uu____22020 =
        match uu____22020 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22034 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22034
       then
         let uu____22035 = wl_to_string wl in
         let uu____22036 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22035 uu____22036
       else ());
      (let g1 =
         let uu____22051 = solve_and_commit env wl fail in
         match uu____22051 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___356_22064 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___356_22064.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___356_22064.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___356_22064.FStar_TypeChecker_Env.implicits)
             }
         | uu____22069 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___357_22073 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___357_22073.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___357_22073.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___357_22073.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22095 = FStar_ST.op_Bang last_proof_ns in
    match uu____22095 with
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
            let uu___358_22279 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___358_22279.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___358_22279.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___358_22279.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22280 =
            let uu____22281 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22281 in
          if uu____22280
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22289 = FStar_TypeChecker_Env.get_range env in
                     let uu____22290 =
                       let uu____22291 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22291 in
                     FStar_Errors.diag uu____22289 uu____22290)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22295 = FStar_TypeChecker_Env.get_range env in
                      let uu____22296 =
                        let uu____22297 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22297 in
                      FStar_Errors.diag uu____22295 uu____22296)
                   else ();
                   (let uu____22299 = check_trivial vc1 in
                    match uu____22299 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22306 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22307 =
                                let uu____22308 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22308 in
                              FStar_Errors.diag uu____22306 uu____22307)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22313 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22314 =
                                let uu____22315 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22315 in
                              FStar_Errors.diag uu____22313 uu____22314)
                           else ();
                           (let vcs =
                              let uu____22326 = FStar_Options.use_tactics () in
                              if uu____22326
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22345  ->
                                     (let uu____22347 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22347);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22349 =
                                   let uu____22356 = FStar_Options.peek () in
                                   (env, vc2, uu____22356) in
                                 [uu____22349]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22390  ->
                                    match uu____22390 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22401 = check_trivial goal1 in
                                        (match uu____22401 with
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
                                                (let uu____22409 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22410 =
                                                   let uu____22411 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22412 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22411 uu____22412 in
                                                 FStar_Errors.diag
                                                   uu____22409 uu____22410)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22415 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22416 =
                                                   let uu____22417 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22417 in
                                                 FStar_Errors.diag
                                                   uu____22415 uu____22416)
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
      let uu____22427 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22427 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22433 =
            let uu____22434 =
              let uu____22439 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22439) in
            FStar_Errors.Error uu____22434 in
          FStar_Exn.raise uu____22433
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22446 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22446 with
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
          let uu____22465 = FStar_Syntax_Unionfind.find u in
          match uu____22465 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22468 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22486 = acc in
          match uu____22486 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22572 = hd1 in
                   (match uu____22572 with
                    | (uu____22585,env,u,tm,k,r) ->
                        let uu____22591 = unresolved u in
                        if uu____22591
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22622 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22622
                            then
                              let uu____22623 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22624 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22625 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22623 uu____22624 uu____22625
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___359_22628 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___359_22628.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___359_22628.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___359_22628.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___359_22628.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___359_22628.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___359_22628.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___359_22628.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___359_22628.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___359_22628.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___359_22628.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___359_22628.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___359_22628.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___359_22628.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___359_22628.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___359_22628.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___359_22628.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___359_22628.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___359_22628.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___359_22628.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___359_22628.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___359_22628.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___359_22628.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___359_22628.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___359_22628.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___359_22628.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___359_22628.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___359_22628.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___359_22628.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___359_22628.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___359_22628.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___359_22628.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___359_22628.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___359_22628.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____22631 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___360_22639 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___360_22639.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___360_22639.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___360_22639.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___360_22639.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___360_22639.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___360_22639.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___360_22639.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___360_22639.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___360_22639.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___360_22639.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___360_22639.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___360_22639.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___360_22639.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___360_22639.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___360_22639.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___360_22639.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___360_22639.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___360_22639.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___360_22639.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___360_22639.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___360_22639.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___360_22639.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___360_22639.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___360_22639.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___360_22639.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___360_22639.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___360_22639.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___360_22639.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___360_22639.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___360_22639.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___360_22639.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___360_22639.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.dep_graph =
                                         (uu___360_22639.FStar_TypeChecker_Env.dep_graph)
                                     }) tm1 in
                                match uu____22631 with
                                | (uu____22640,uu____22641,g1) -> g1
                              else
                                (let uu____22644 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___361_22652 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___361_22652.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___361_22652.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___361_22652.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___361_22652.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___361_22652.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___361_22652.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___361_22652.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___361_22652.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___361_22652.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___361_22652.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___361_22652.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___361_22652.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___361_22652.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___361_22652.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___361_22652.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___361_22652.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___361_22652.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___361_22652.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___361_22652.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___361_22652.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___361_22652.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___361_22652.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___361_22652.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___361_22652.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___361_22652.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___361_22652.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___361_22652.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___361_22652.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___361_22652.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___361_22652.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___361_22652.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___361_22652.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___361_22652.FStar_TypeChecker_Env.dep_graph)
                                      }) tm1 in
                                 match uu____22644 with
                                 | (uu____22653,uu____22654,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___362_22657 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___362_22657.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___362_22657.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___362_22657.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____22660 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____22666  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____22660 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___363_22694 = g in
        let uu____22695 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___363_22694.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___363_22694.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___363_22694.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____22695
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
        let uu____22749 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22749 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22762 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22762
      | (reason,uu____22764,uu____22765,e,t,r)::uu____22769 ->
          let uu____22796 =
            let uu____22797 =
              let uu____22802 =
                let uu____22803 = FStar_Syntax_Print.term_to_string t in
                let uu____22804 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22803 uu____22804 in
              (uu____22802, r) in
            FStar_Errors.Error uu____22797 in
          FStar_Exn.raise uu____22796
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___364_22811 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___364_22811.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___364_22811.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___364_22811.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22837 = try_teq false env t1 t2 in
        match uu____22837 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____22841 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____22841 with
             | FStar_Pervasives_Native.Some uu____22846 -> true
             | FStar_Pervasives_Native.None  -> false)