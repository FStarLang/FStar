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
        let uu____3244 =
          let uu____3251 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3251 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3244
          (FStar_Util.for_some
             (fun uu____3287  ->
                match uu____3287 with
                | (uv,uu____3293) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3300 'Auu____3301 .
    'Auu____3301 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3300)
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
            let uu____3333 = occurs wl uk t in Prims.op_Negation uu____3333 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3340 =
                 let uu____3341 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3342 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3341 uu____3342 in
               FStar_Pervasives_Native.Some uu____3340) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3352 'Auu____3353 .
    'Auu____3353 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3352)
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
            let uu____3407 = occurs_check env wl uk t in
            match uu____3407 with
            | (occurs_ok,msg) ->
                let uu____3438 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3438, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3461 'Auu____3462 .
    (FStar_Syntax_Syntax.bv,'Auu____3462) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3461) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3461) FStar_Pervasives_Native.tuple2
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
      let uu____3546 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3600  ->
                fun uu____3601  ->
                  match (uu____3600, uu____3601) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3682 =
                        let uu____3683 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3683 in
                      if uu____3682
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3708 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3708
                         then
                           let uu____3721 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3721)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3546 with | (isect,uu____3762) -> FStar_List.rev isect
let binders_eq:
  'Auu____3787 'Auu____3788 .
    (FStar_Syntax_Syntax.bv,'Auu____3788) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3787) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3843  ->
              fun uu____3844  ->
                match (uu____3843, uu____3844) with
                | ((a,uu____3862),(b,uu____3864)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3878 'Auu____3879 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3879) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3878)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3878)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____3930 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____3944  ->
                      match uu____3944 with
                      | (b,uu____3950) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____3930
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____3966 -> FStar_Pervasives_Native.None
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
            let uu____4038 = pat_var_opt env seen hd1 in
            (match uu____4038 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4052 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4052
                   then
                     let uu____4053 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4053
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4071 =
      let uu____4072 = FStar_Syntax_Subst.compress t in
      uu____4072.FStar_Syntax_Syntax.n in
    match uu____4071 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4075 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4092;
           FStar_Syntax_Syntax.pos = uu____4093;
           FStar_Syntax_Syntax.vars = uu____4094;_},uu____4095)
        -> true
    | uu____4132 -> false
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
           FStar_Syntax_Syntax.pos = uu____4256;
           FStar_Syntax_Syntax.vars = uu____4257;_},args)
        -> (t, uv, k, args)
    | uu____4325 -> failwith "Not a flex-uvar"
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
      let uu____4402 = destruct_flex_t t in
      match uu____4402 with
      | (t1,uv,k,args) ->
          let uu____4517 = pat_vars env [] args in
          (match uu____4517 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4615 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4696 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4731 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4735 -> false
let head_match: match_result -> match_result =
  fun uu___293_4738  ->
    match uu___293_4738 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4753 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4762 ->
          let uu____4763 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4763 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4774 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4793 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4802 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4829 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4830 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4831 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4848 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4861 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4885) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4891,uu____4892) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____4934) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____4955;
             FStar_Syntax_Syntax.index = uu____4956;
             FStar_Syntax_Syntax.sort = t2;_},uu____4958)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____4965 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____4966 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____4967 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____4980 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____4998 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____4998
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
            let uu____5019 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5019
            then FullMatch
            else
              (let uu____5021 =
                 let uu____5030 =
                   let uu____5033 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5033 in
                 let uu____5034 =
                   let uu____5037 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5037 in
                 (uu____5030, uu____5034) in
               MisMatch uu____5021)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5043),FStar_Syntax_Syntax.Tm_uinst (g,uu____5045)) ->
            let uu____5054 = head_matches env f g in
            FStar_All.pipe_right uu____5054 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5057 = FStar_Const.eq_const c d in
            if uu____5057
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5064),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5066)) ->
            let uu____5115 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5115
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5122),FStar_Syntax_Syntax.Tm_refine (y,uu____5124)) ->
            let uu____5133 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5133 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5135),uu____5136) ->
            let uu____5141 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5141 head_match
        | (uu____5142,FStar_Syntax_Syntax.Tm_refine (x,uu____5144)) ->
            let uu____5149 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5149 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5150,FStar_Syntax_Syntax.Tm_type
           uu____5151) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5152,FStar_Syntax_Syntax.Tm_arrow uu____5153) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5179),FStar_Syntax_Syntax.Tm_app (head',uu____5181))
            ->
            let uu____5222 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5222 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5224),uu____5225) ->
            let uu____5246 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5246 head_match
        | (uu____5247,FStar_Syntax_Syntax.Tm_app (head1,uu____5249)) ->
            let uu____5270 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5270 head_match
        | uu____5271 ->
            let uu____5276 =
              let uu____5285 = delta_depth_of_term env t11 in
              let uu____5288 = delta_depth_of_term env t21 in
              (uu____5285, uu____5288) in
            MisMatch uu____5276
let head_matches_delta:
  'Auu____5300 .
    FStar_TypeChecker_Env.env ->
      'Auu____5300 ->
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
            let uu____5333 = FStar_Syntax_Util.head_and_args t in
            match uu____5333 with
            | (head1,uu____5351) ->
                let uu____5372 =
                  let uu____5373 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5373.FStar_Syntax_Syntax.n in
                (match uu____5372 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5379 =
                       let uu____5380 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5380 FStar_Option.isSome in
                     if uu____5379
                     then
                       let uu____5399 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5399
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5403 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5506)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5524 =
                     let uu____5533 = maybe_inline t11 in
                     let uu____5536 = maybe_inline t21 in
                     (uu____5533, uu____5536) in
                   match uu____5524 with
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
                (uu____5573,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5591 =
                     let uu____5600 = maybe_inline t11 in
                     let uu____5603 = maybe_inline t21 in
                     (uu____5600, uu____5603) in
                   match uu____5591 with
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
                let uu____5646 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5646 with
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
                let uu____5669 =
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
                (match uu____5669 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5693 -> fail r
            | uu____5702 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5735 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____5771 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___294_5783  ->
    match uu___294_5783 with
    | T (t,uu____5785) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5801 = FStar_Syntax_Util.type_u () in
      match uu____5801 with
      | (t,uu____5807) ->
          let uu____5808 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____5808
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5819 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____5819 FStar_Pervasives_Native.fst
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
        let uu____5883 = head_matches env t1 t' in
        match uu____5883 with
        | MisMatch uu____5884 -> false
        | uu____5893 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____5989,imp),T (t2,uu____5992)) -> (t2, imp)
                     | uu____6011 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6078  ->
                    match uu____6078 with
                    | (t2,uu____6092) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6135 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6135 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6210))::tcs2) ->
                       aux
                         (((let uu___318_6245 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___318_6245.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___318_6245.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6263 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___295_6316 =
                 match uu___295_6316 with
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
               let uu____6433 = decompose1 [] bs1 in
               (rebuild, matches, uu____6433))
      | uu____6482 ->
          let rebuild uu___296_6488 =
            match uu___296_6488 with
            | [] -> t1
            | uu____6491 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___297_6522  ->
    match uu___297_6522 with
    | T (t,uu____6524) -> t
    | uu____6533 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___298_6536  ->
    match uu___298_6536 with
    | T (t,uu____6538) -> FStar_Syntax_Syntax.as_arg t
    | uu____6547 -> failwith "Impossible"
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
              | (uu____6653,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6678 = new_uvar r scope1 k in
                  (match uu____6678 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6696 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6713 =
                         let uu____6714 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6714 in
                       ((T (gi_xs, mk_kind)), uu____6713))
              | (uu____6727,uu____6728,C uu____6729) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____6876 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6893;
                         FStar_Syntax_Syntax.vars = uu____6894;_})
                        ->
                        let uu____6917 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6917 with
                         | (T (gi_xs,uu____6941),prob) ->
                             let uu____6951 =
                               let uu____6952 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____6952 in
                             (uu____6951, [prob])
                         | uu____6955 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6970;
                         FStar_Syntax_Syntax.vars = uu____6971;_})
                        ->
                        let uu____6994 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6994 with
                         | (T (gi_xs,uu____7018),prob) ->
                             let uu____7028 =
                               let uu____7029 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7029 in
                             (uu____7028, [prob])
                         | uu____7032 -> failwith "impossible")
                    | (uu____7043,uu____7044,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7046;
                         FStar_Syntax_Syntax.vars = uu____7047;_})
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
                        let uu____7178 =
                          let uu____7187 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7187 FStar_List.unzip in
                        (match uu____7178 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7241 =
                                 let uu____7242 =
                                   let uu____7245 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7245 un_T in
                                 let uu____7246 =
                                   let uu____7255 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7255
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7242;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7246;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7241 in
                             ((C gi_xs), sub_probs))
                    | uu____7264 ->
                        let uu____7277 = sub_prob scope1 args q in
                        (match uu____7277 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____6876 with
                   | (tc,probs) ->
                       let uu____7308 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7371,uu____7372),T
                            (t,uu____7374)) ->
                             let b1 =
                               ((let uu___319_7411 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___319_7411.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___319_7411.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7412 =
                               let uu____7419 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7419 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7412)
                         | uu____7454 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7308 with
                        | (bopt,scope2,args1) ->
                            let uu____7538 = aux scope2 args1 qs2 in
                            (match uu____7538 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7575 =
                                         let uu____7578 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7578 in
                                       FStar_Syntax_Util.mk_conj_l uu____7575
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7601 =
                                         let uu____7604 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7605 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7604 :: uu____7605 in
                                       FStar_Syntax_Util.mk_conj_l uu____7601 in
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
  'Auu____7673 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7673)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7673)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___320_7694 = p in
      let uu____7699 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7700 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___320_7694.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7699;
        FStar_TypeChecker_Common.relation =
          (uu___320_7694.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7700;
        FStar_TypeChecker_Common.element =
          (uu___320_7694.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___320_7694.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___320_7694.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___320_7694.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___320_7694.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___320_7694.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7712 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7712
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7721 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____7741 = compress_prob wl pr in
        FStar_All.pipe_right uu____7741 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7751 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____7751 with
           | (lh,uu____7771) ->
               let uu____7792 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____7792 with
                | (rh,uu____7812) ->
                    let uu____7833 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7850,FStar_Syntax_Syntax.Tm_uvar uu____7851)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7888,uu____7889)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____7910,FStar_Syntax_Syntax.Tm_uvar uu____7911)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7932,uu____7933)
                          ->
                          let uu____7950 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____7950 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____7999 ->
                                    let rank =
                                      let uu____8007 = is_top_level_prob prob in
                                      if uu____8007
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8009 =
                                      let uu___321_8014 = tp in
                                      let uu____8019 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___321_8014.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___321_8014.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___321_8014.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8019;
                                        FStar_TypeChecker_Common.element =
                                          (uu___321_8014.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___321_8014.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___321_8014.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___321_8014.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___321_8014.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___321_8014.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8009)))
                      | (uu____8030,FStar_Syntax_Syntax.Tm_uvar uu____8031)
                          ->
                          let uu____8048 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8048 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8097 ->
                                    let uu____8104 =
                                      let uu___322_8111 = tp in
                                      let uu____8116 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___322_8111.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8116;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___322_8111.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___322_8111.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___322_8111.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___322_8111.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___322_8111.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___322_8111.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___322_8111.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___322_8111.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8104)))
                      | (uu____8133,uu____8134) -> (rigid_rigid, tp) in
                    (match uu____7833 with
                     | (rank,tp1) ->
                         let uu____8153 =
                           FStar_All.pipe_right
                             (let uu___323_8159 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___323_8159.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___323_8159.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___323_8159.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___323_8159.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___323_8159.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___323_8159.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___323_8159.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___323_8159.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___323_8159.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8153))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8169 =
            FStar_All.pipe_right
              (let uu___324_8175 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___324_8175.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___324_8175.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___324_8175.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___324_8175.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___324_8175.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___324_8175.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___324_8175.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___324_8175.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___324_8175.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8169)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8230 probs =
      match uu____8230 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8283 = rank wl hd1 in
               (match uu____8283 with
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
    match projectee with | UDeferred _0 -> true | uu____8390 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8402 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8414 -> false
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
                        let uu____8454 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8454 with
                        | (k,uu____8460) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8470 -> false)))
            | uu____8471 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8522 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8522 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8525 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8535 =
                     let uu____8536 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8537 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8536
                       uu____8537 in
                   UFailed uu____8535)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8557 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8557 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8579 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8579 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8582 ->
                let uu____8587 =
                  let uu____8588 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8589 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8588
                    uu____8589 msg in
                UFailed uu____8587 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8590,uu____8591) ->
              let uu____8592 =
                let uu____8593 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8594 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8593 uu____8594 in
              failwith uu____8592
          | (FStar_Syntax_Syntax.U_unknown ,uu____8595) ->
              let uu____8596 =
                let uu____8597 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8598 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8597 uu____8598 in
              failwith uu____8596
          | (uu____8599,FStar_Syntax_Syntax.U_bvar uu____8600) ->
              let uu____8601 =
                let uu____8602 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8603 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8602 uu____8603 in
              failwith uu____8601
          | (uu____8604,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8605 =
                let uu____8606 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8607 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8606 uu____8607 in
              failwith uu____8605
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8631 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8631
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8653 = occurs_univ v1 u3 in
              if uu____8653
              then
                let uu____8654 =
                  let uu____8655 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8656 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8655 uu____8656 in
                try_umax_components u11 u21 uu____8654
              else
                (let uu____8658 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8658)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8678 = occurs_univ v1 u3 in
              if uu____8678
              then
                let uu____8679 =
                  let uu____8680 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8681 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8680 uu____8681 in
                try_umax_components u11 u21 uu____8679
              else
                (let uu____8683 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8683)
          | (FStar_Syntax_Syntax.U_max uu____8692,uu____8693) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8699 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8699
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8701,FStar_Syntax_Syntax.U_max uu____8702) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8708 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8708
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8710,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8711,FStar_Syntax_Syntax.U_name
             uu____8712) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8713) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8714) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8715,FStar_Syntax_Syntax.U_succ
             uu____8716) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8717,FStar_Syntax_Syntax.U_zero
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
      let uu____8803 = bc1 in
      match uu____8803 with
      | (bs1,mk_cod1) ->
          let uu____8844 = bc2 in
          (match uu____8844 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____8914 = FStar_Util.first_N n1 bs in
                 match uu____8914 with
                 | (bs3,rest) ->
                     let uu____8939 = mk_cod rest in (bs3, uu____8939) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____8968 =
                   let uu____8975 = mk_cod1 [] in (bs1, uu____8975) in
                 let uu____8978 =
                   let uu____8985 = mk_cod2 [] in (bs2, uu____8985) in
                 (uu____8968, uu____8978)
               else
                 if l1 > l2
                 then
                   (let uu____9027 = curry l2 bs1 mk_cod1 in
                    let uu____9040 =
                      let uu____9047 = mk_cod2 [] in (bs2, uu____9047) in
                    (uu____9027, uu____9040))
                 else
                   (let uu____9063 =
                      let uu____9070 = mk_cod1 [] in (bs1, uu____9070) in
                    let uu____9073 = curry l1 bs2 mk_cod2 in
                    (uu____9063, uu____9073)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9194 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9194
       then
         let uu____9195 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9195
       else ());
      (let uu____9197 = next_prob probs in
       match uu____9197 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___325_9218 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___325_9218.wl_deferred);
               ctr = (uu___325_9218.ctr);
               defer_ok = (uu___325_9218.defer_ok);
               smt_ok = (uu___325_9218.smt_ok);
               tcenv = (uu___325_9218.tcenv)
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
                  let uu____9229 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9229 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9234 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9234 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9239,uu____9240) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9257 ->
                let uu____9266 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9325  ->
                          match uu____9325 with
                          | (c,uu____9333,uu____9334) -> c < probs.ctr)) in
                (match uu____9266 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9375 =
                            FStar_List.map
                              (fun uu____9390  ->
                                 match uu____9390 with
                                 | (uu____9401,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9375
                      | uu____9404 ->
                          let uu____9413 =
                            let uu___326_9414 = probs in
                            let uu____9415 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9436  ->
                                      match uu____9436 with
                                      | (uu____9443,uu____9444,y) -> y)) in
                            {
                              attempting = uu____9415;
                              wl_deferred = rest;
                              ctr = (uu___326_9414.ctr);
                              defer_ok = (uu___326_9414.defer_ok);
                              smt_ok = (uu___326_9414.smt_ok);
                              tcenv = (uu___326_9414.tcenv)
                            } in
                          solve env uu____9413))))
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
            let uu____9451 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9451 with
            | USolved wl1 ->
                let uu____9453 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9453
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
                  let uu____9499 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9499 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9502 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9514;
                  FStar_Syntax_Syntax.vars = uu____9515;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9518;
                  FStar_Syntax_Syntax.vars = uu____9519;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9533,uu____9534) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9541,FStar_Syntax_Syntax.Tm_uinst uu____9542) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9549 -> USolved wl
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
            ((let uu____9559 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9559
              then
                let uu____9560 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9560 msg
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
        (let uu____9569 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9569
         then
           let uu____9570 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9570
         else ());
        (let uu____9572 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9572 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9634 = head_matches_delta env () t1 t2 in
               match uu____9634 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9675 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____9724 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9739 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____9740 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____9739, uu____9740)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9745 = FStar_Syntax_Subst.compress t1 in
                              let uu____9746 = FStar_Syntax_Subst.compress t2 in
                              (uu____9745, uu____9746) in
                        (match uu____9724 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____9772 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____9772 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____9803 =
                                    let uu____9812 =
                                      let uu____9815 =
                                        let uu____9818 =
                                          let uu____9819 =
                                            let uu____9826 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____9826) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____9819 in
                                        FStar_Syntax_Syntax.mk uu____9818 in
                                      uu____9815 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____9834 =
                                      let uu____9837 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____9837] in
                                    (uu____9812, uu____9834) in
                                  FStar_Pervasives_Native.Some uu____9803
                              | (uu____9850,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9852)) ->
                                  let uu____9857 =
                                    let uu____9864 =
                                      let uu____9867 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____9867] in
                                    (t11, uu____9864) in
                                  FStar_Pervasives_Native.Some uu____9857
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9877),uu____9878) ->
                                  let uu____9883 =
                                    let uu____9890 =
                                      let uu____9893 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____9893] in
                                    (t21, uu____9890) in
                                  FStar_Pervasives_Native.Some uu____9883
                              | uu____9902 ->
                                  let uu____9907 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____9907 with
                                   | (head1,uu____9931) ->
                                       let uu____9952 =
                                         let uu____9953 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____9953.FStar_Syntax_Syntax.n in
                                       (match uu____9952 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____9964;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____9966;_}
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
                                        | uu____9973 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____9986) ->
                  let uu____10011 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___299_10037  ->
                            match uu___299_10037 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10044 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10044 with
                                      | (u',uu____10060) ->
                                          let uu____10081 =
                                            let uu____10082 = whnf env u' in
                                            uu____10082.FStar_Syntax_Syntax.n in
                                          (match uu____10081 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10086) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10111 -> false))
                                 | uu____10112 -> false)
                            | uu____10115 -> false)) in
                  (match uu____10011 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10149 tps =
                         match uu____10149 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10197 =
                                    let uu____10206 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10206 in
                                  (match uu____10197 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10241 -> FStar_Pervasives_Native.None) in
                       let uu____10250 =
                         let uu____10259 =
                           let uu____10266 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10266, []) in
                         make_lower_bound uu____10259 lower_bounds in
                       (match uu____10250 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10278 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10278
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
                            ((let uu____10298 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10298
                              then
                                let wl' =
                                  let uu___327_10300 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___327_10300.wl_deferred);
                                    ctr = (uu___327_10300.ctr);
                                    defer_ok = (uu___327_10300.defer_ok);
                                    smt_ok = (uu___327_10300.smt_ok);
                                    tcenv = (uu___327_10300.tcenv)
                                  } in
                                let uu____10301 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10301
                              else ());
                             (let uu____10303 =
                                solve_t env eq_prob
                                  (let uu___328_10305 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___328_10305.wl_deferred);
                                     ctr = (uu___328_10305.ctr);
                                     defer_ok = (uu___328_10305.defer_ok);
                                     smt_ok = (uu___328_10305.smt_ok);
                                     tcenv = (uu___328_10305.tcenv)
                                   }) in
                              match uu____10303 with
                              | Success uu____10308 ->
                                  let wl1 =
                                    let uu___329_10310 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___329_10310.wl_deferred);
                                      ctr = (uu___329_10310.ctr);
                                      defer_ok = (uu___329_10310.defer_ok);
                                      smt_ok = (uu___329_10310.smt_ok);
                                      tcenv = (uu___329_10310.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10312 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10317 -> FStar_Pervasives_Native.None))))
              | uu____10318 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10327 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10327
         then
           let uu____10328 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10328
         else ());
        (let uu____10330 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10330 with
         | (u,args) ->
             let uu____10369 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10369 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10410 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10410 with
                    | (h1,args1) ->
                        let uu____10451 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10451 with
                         | (h2,uu____10471) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10498 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10498
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10516 =
                                          let uu____10519 =
                                            let uu____10520 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10520 in
                                          [uu____10519] in
                                        FStar_Pervasives_Native.Some
                                          uu____10516))
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
                                       (let uu____10553 =
                                          let uu____10556 =
                                            let uu____10557 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10557 in
                                          [uu____10556] in
                                        FStar_Pervasives_Native.Some
                                          uu____10553))
                                  else FStar_Pervasives_Native.None
                              | uu____10571 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10661 =
                               let uu____10670 =
                                 let uu____10673 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10673 in
                               (uu____10670, m1) in
                             FStar_Pervasives_Native.Some uu____10661)
                    | (uu____10686,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10688)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____10736),uu____10737) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____10784 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10837) ->
                       let uu____10862 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___300_10888  ->
                                 match uu___300_10888 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____10895 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____10895 with
                                           | (u',uu____10911) ->
                                               let uu____10932 =
                                                 let uu____10933 =
                                                   whnf env u' in
                                                 uu____10933.FStar_Syntax_Syntax.n in
                                               (match uu____10932 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____10937) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____10962 -> false))
                                      | uu____10963 -> false)
                                 | uu____10966 -> false)) in
                       (match uu____10862 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11004 tps =
                              match uu____11004 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11066 =
                                         let uu____11077 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11077 in
                                       (match uu____11066 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11128 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11139 =
                              let uu____11150 =
                                let uu____11159 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11159, []) in
                              make_upper_bound uu____11150 upper_bounds in
                            (match uu____11139 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11173 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11173
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
                                 ((let uu____11199 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11199
                                   then
                                     let wl' =
                                       let uu___330_11201 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___330_11201.wl_deferred);
                                         ctr = (uu___330_11201.ctr);
                                         defer_ok = (uu___330_11201.defer_ok);
                                         smt_ok = (uu___330_11201.smt_ok);
                                         tcenv = (uu___330_11201.tcenv)
                                       } in
                                     let uu____11202 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11202
                                   else ());
                                  (let uu____11204 =
                                     solve_t env eq_prob
                                       (let uu___331_11206 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___331_11206.wl_deferred);
                                          ctr = (uu___331_11206.ctr);
                                          defer_ok =
                                            (uu___331_11206.defer_ok);
                                          smt_ok = (uu___331_11206.smt_ok);
                                          tcenv = (uu___331_11206.tcenv)
                                        }) in
                                   match uu____11204 with
                                   | Success uu____11209 ->
                                       let wl1 =
                                         let uu___332_11211 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___332_11211.wl_deferred);
                                           ctr = (uu___332_11211.ctr);
                                           defer_ok =
                                             (uu___332_11211.defer_ok);
                                           smt_ok = (uu___332_11211.smt_ok);
                                           tcenv = (uu___332_11211.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11213 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11218 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11219 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11294 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11294
                      then
                        let uu____11295 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11295
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___333_11349 = hd1 in
                      let uu____11350 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___333_11349.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___333_11349.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11350
                      } in
                    let hd21 =
                      let uu___334_11354 = hd2 in
                      let uu____11355 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___334_11354.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___334_11354.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11355
                      } in
                    let prob =
                      let uu____11359 =
                        let uu____11364 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11364 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11359 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11375 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11375 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11379 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11379 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11417 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11422 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11417 uu____11422 in
                         ((let uu____11432 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11432
                           then
                             let uu____11433 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11434 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11433 uu____11434
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11457 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11467 = aux scope env [] bs1 bs2 in
              match uu____11467 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11491 = compress_tprob wl problem in
        solve_t' env uu____11491 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11524 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11524 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11555,uu____11556) ->
                   let rec may_relate head3 =
                     let uu____11581 =
                       let uu____11582 = FStar_Syntax_Subst.compress head3 in
                       uu____11582.FStar_Syntax_Syntax.n in
                     match uu____11581 with
                     | FStar_Syntax_Syntax.Tm_name uu____11585 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11586 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11609;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11610;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11613;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11614;
                           FStar_Syntax_Syntax.fv_qual = uu____11615;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11619,uu____11620) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11662) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11668) ->
                         may_relate t
                     | uu____11673 -> false in
                   let uu____11674 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11674
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
                                let uu____11691 =
                                  let uu____11692 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11692 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11691 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11694 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11694
                   else
                     (let uu____11696 =
                        let uu____11697 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11698 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11697 uu____11698 in
                      giveup env1 uu____11696 orig)
               | (uu____11699,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___335_11713 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___335_11713.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___335_11713.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___335_11713.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___335_11713.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___335_11713.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___335_11713.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___335_11713.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___335_11713.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____11714,FStar_Pervasives_Native.None ) ->
                   ((let uu____11726 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____11726
                     then
                       let uu____11727 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11728 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____11729 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____11730 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____11727
                         uu____11728 uu____11729 uu____11730
                     else ());
                    (let uu____11732 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____11732 with
                     | (head11,args1) ->
                         let uu____11769 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____11769 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____11823 =
                                  let uu____11824 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____11825 = args_to_string args1 in
                                  let uu____11826 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____11827 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____11824 uu____11825 uu____11826
                                    uu____11827 in
                                giveup env1 uu____11823 orig
                              else
                                (let uu____11829 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____11835 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____11835 = FStar_Syntax_Util.Equal) in
                                 if uu____11829
                                 then
                                   let uu____11836 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____11836 with
                                   | USolved wl2 ->
                                       let uu____11838 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____11838
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____11842 =
                                      base_and_refinement env1 t1 in
                                    match uu____11842 with
                                    | (base1,refinement1) ->
                                        let uu____11867 =
                                          base_and_refinement env1 t2 in
                                        (match uu____11867 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____11924 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____11924 with
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
                                                           (fun uu____11946 
                                                              ->
                                                              fun uu____11947
                                                                 ->
                                                                match 
                                                                  (uu____11946,
                                                                    uu____11947)
                                                                with
                                                                | ((a,uu____11965),
                                                                   (a',uu____11967))
                                                                    ->
                                                                    let uu____11976
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
                                                                    uu____11976)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____11986 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____11986 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____11992 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___336_12028 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___336_12028.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12067 =
          match uu____12067 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12283  ->
                              match uu____12283 with
                              | (x,imp) ->
                                  let uu____12294 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12294, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12307 = FStar_Syntax_Util.type_u () in
                      match uu____12307 with
                      | (t1,uu____12313) ->
                          let uu____12314 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12314 in
                    let uu____12319 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12319 with
                     | (t',tm_u1) ->
                         let uu____12332 = destruct_flex_t t' in
                         (match uu____12332 with
                          | (uu____12369,u1,k1,uu____12372) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12431 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12431 in
                              let sol =
                                let uu____12435 =
                                  let uu____12444 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12444) in
                                TERM uu____12435 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____12580 = pat_var_opt env pat_args hd1 in
                    (match uu____12580 with
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
                                    (fun uu____12643  ->
                                       match uu____12643 with
                                       | (x,uu____12649) ->
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
                            let uu____12664 =
                              let uu____12665 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____12665 in
                            if uu____12664
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____12677 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____12677 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____12692::uu____12693) ->
                    let uu____12724 =
                      let uu____12737 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____12737 in
                    (match uu____12724 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____12776 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____12783::uu____12784,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____12819 =
                let uu____12832 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____12832 in
              (match uu____12819 with
               | (all_formals,res_t) ->
                   let uu____12857 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____12857 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____12891 = lhs in
          match uu____12891 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____12901 ->
                    let uu____12902 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____12902 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____12925 = p in
          match uu____12925 with
          | (((u,k),xs,c),ps,(h,uu____12936,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13018 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13018 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13041 = h gs_xs in
                     let uu____13042 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13041 uu____13042 in
                   ((let uu____13048 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13048
                     then
                       let uu____13049 =
                         let uu____13052 =
                           let uu____13053 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13053
                             (FStar_String.concat "\n\t") in
                         let uu____13058 =
                           let uu____13061 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13062 =
                             let uu____13065 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13066 =
                               let uu____13069 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13070 =
                                 let uu____13073 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13074 =
                                   let uu____13077 =
                                     let uu____13078 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13078
                                       (FStar_String.concat ", ") in
                                   let uu____13083 =
                                     let uu____13086 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13086] in
                                   uu____13077 :: uu____13083 in
                                 uu____13073 :: uu____13074 in
                               uu____13069 :: uu____13070 in
                             uu____13065 :: uu____13066 in
                           uu____13061 :: uu____13062 in
                         uu____13052 :: uu____13058 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13049
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___301_13107 =
          match uu___301_13107 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13139 = p in
          match uu____13139 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13230 = FStar_List.nth ps i in
              (match uu____13230 with
               | (pi,uu____13234) ->
                   let uu____13239 = FStar_List.nth xs i in
                   (match uu____13239 with
                    | (xi,uu____13251) ->
                        let rec gs k =
                          let uu____13264 =
                            let uu____13277 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13277 in
                          match uu____13264 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13352)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13365 = new_uvar r xs k_a in
                                    (match uu____13365 with
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
                                         let uu____13387 = aux subst2 tl1 in
                                         (match uu____13387 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13414 =
                                                let uu____13417 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13417 :: gi_xs' in
                                              let uu____13418 =
                                                let uu____13421 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13421 :: gi_ps' in
                                              (uu____13414, uu____13418))) in
                              aux [] bs in
                        let uu____13426 =
                          let uu____13427 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13427 in
                        if uu____13426
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13431 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13431 with
                           | (g_xs,uu____13443) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13454 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13455 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13454
                                   uu____13455 in
                               let sub1 =
                                 let uu____13461 =
                                   let uu____13466 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13469 =
                                     let uu____13472 =
                                       FStar_List.map
                                         (fun uu____13487  ->
                                            match uu____13487 with
                                            | (uu____13496,uu____13497,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13472 in
                                   mk_problem (p_scope orig) orig uu____13466
                                     (p_rel orig) uu____13469
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13461 in
                               ((let uu____13512 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13512
                                 then
                                   let uu____13513 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13514 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13513 uu____13514
                                 else ());
                                (let wl2 =
                                   let uu____13517 =
                                     let uu____13520 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13520 in
                                   solve_prob orig uu____13517
                                     [TERM (u, proj)] wl1 in
                                 let uu____13529 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13529))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13560 = lhs in
          match uu____13560 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13596 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13596 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13629 =
                        let uu____13676 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13676) in
                      FStar_Pervasives_Native.Some uu____13629
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____13820 =
                           let uu____13827 =
                             let uu____13828 = FStar_Syntax_Subst.compress k1 in
                             uu____13828.FStar_Syntax_Syntax.n in
                           (uu____13827, args) in
                         match uu____13820 with
                         | (uu____13839,[]) ->
                             let uu____13842 =
                               let uu____13853 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____13853) in
                             FStar_Pervasives_Native.Some uu____13842
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13874,uu____13875) ->
                             let uu____13896 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____13896 with
                              | (uv1,uv_args) ->
                                  let uu____13939 =
                                    let uu____13940 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13940.FStar_Syntax_Syntax.n in
                                  (match uu____13939 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13950) ->
                                       let uu____13975 =
                                         pat_vars env [] uv_args in
                                       (match uu____13975 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14002  ->
                                                      let uu____14003 =
                                                        let uu____14004 =
                                                          let uu____14005 =
                                                            let uu____14010 =
                                                              let uu____14011
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14011
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14010 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14005 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14004 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14003)) in
                                            let c1 =
                                              let uu____14021 =
                                                let uu____14022 =
                                                  let uu____14027 =
                                                    let uu____14028 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14028
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14027 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14022 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14021 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14041 =
                                                let uu____14044 =
                                                  let uu____14045 =
                                                    let uu____14048 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14048
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14045 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14044 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14041 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14066 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14071,uu____14072) ->
                             let uu____14091 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14091 with
                              | (uv1,uv_args) ->
                                  let uu____14134 =
                                    let uu____14135 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14135.FStar_Syntax_Syntax.n in
                                  (match uu____14134 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14145) ->
                                       let uu____14170 =
                                         pat_vars env [] uv_args in
                                       (match uu____14170 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14197  ->
                                                      let uu____14198 =
                                                        let uu____14199 =
                                                          let uu____14200 =
                                                            let uu____14205 =
                                                              let uu____14206
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14206
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14205 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14200 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14199 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14198)) in
                                            let c1 =
                                              let uu____14216 =
                                                let uu____14217 =
                                                  let uu____14222 =
                                                    let uu____14223 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14223
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14222 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14217 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14216 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14236 =
                                                let uu____14239 =
                                                  let uu____14240 =
                                                    let uu____14243 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14243
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14240 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14239 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14236 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14261 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14268) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14309 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14309
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14345 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14345 with
                                  | (args1,rest) ->
                                      let uu____14374 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14374 with
                                       | (xs2,c2) ->
                                           let uu____14387 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14387
                                             (fun uu____14411  ->
                                                match uu____14411 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14451 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14451 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14519 =
                                        let uu____14524 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14524 in
                                      FStar_All.pipe_right uu____14519
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14539 ->
                             let uu____14546 =
                               let uu____14547 =
                                 let uu____14552 =
                                   let uu____14553 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14554 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14555 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14553 uu____14554 uu____14555 in
                                 (uu____14552, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14547 in
                             FStar_Exn.raise uu____14546 in
                       let uu____14562 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14562
                         (fun uu____14617  ->
                            match uu____14617 with
                            | (xs1,c1) ->
                                let uu____14666 =
                                  let uu____14707 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____14707) in
                                FStar_Pervasives_Native.Some uu____14666)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____14828 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____14844 = project orig env wl1 i st in
                     match uu____14844 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____14858) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____14873 = imitate orig env wl1 st in
                  match uu____14873 with
                  | Failed uu____14878 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____14909 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____14909 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____14934 =
                      let uu____14935 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____14935 wl2 in
                    (match uu____14934 with
                     | Failed uu____14936 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____14954 = FStar_Syntax_Util.head_and_args t21 in
                match uu____14954 with
                | (hd1,uu____14970) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____14991 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15004 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15005 -> true
                     | uu____15022 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15026 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15026
                         then true
                         else
                           ((let uu____15029 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15029
                             then
                               let uu____15030 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15030
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15050 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15050 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15063 =
                            let uu____15064 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15064 in
                          giveup_or_defer1 orig uu____15063
                        else
                          (let uu____15066 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15066
                           then
                             let uu____15067 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15067
                              then
                                let uu____15068 = subterms args_lhs in
                                imitate' orig env wl1 uu____15068
                              else
                                ((let uu____15073 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15073
                                  then
                                    let uu____15074 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15075 = names_to_string fvs1 in
                                    let uu____15076 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15074 uu____15075 uu____15076
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
                               (let uu____15080 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15080
                                then
                                  ((let uu____15082 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15082
                                    then
                                      let uu____15083 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15084 = names_to_string fvs1 in
                                      let uu____15085 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15083 uu____15084 uu____15085
                                    else ());
                                   (let uu____15087 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15087))
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
                     (let uu____15098 =
                        let uu____15099 = FStar_Syntax_Free.names t1 in
                        check_head uu____15099 t2 in
                      if uu____15098
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15110 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15110
                          then
                            let uu____15111 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15112 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15111 uu____15112
                          else ());
                         (let uu____15120 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15120))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15197 uu____15198 r =
               match (uu____15197, uu____15198) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15396 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15396
                   then
                     let uu____15397 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15397
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15421 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15421
                       then
                         let uu____15422 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15423 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15424 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15425 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15426 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15422 uu____15423 uu____15424 uu____15425
                           uu____15426
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15486 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15486 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15500 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15500 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15554 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15554 in
                                  let uu____15557 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15557 k3)
                           else
                             (let uu____15561 =
                                let uu____15562 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15563 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15564 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15562 uu____15563 uu____15564 in
                              failwith uu____15561) in
                       let uu____15565 =
                         let uu____15572 =
                           let uu____15585 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15585 in
                         match uu____15572 with
                         | (bs,k1') ->
                             let uu____15610 =
                               let uu____15623 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15623 in
                             (match uu____15610 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15651 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15651 in
                                  let uu____15660 =
                                    let uu____15665 =
                                      let uu____15666 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15666.FStar_Syntax_Syntax.n in
                                    let uu____15669 =
                                      let uu____15670 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15670.FStar_Syntax_Syntax.n in
                                    (uu____15665, uu____15669) in
                                  (match uu____15660 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15679,uu____15680) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____15683,FStar_Syntax_Syntax.Tm_type
                                      uu____15684) -> (k2'_ys, [sub_prob])
                                   | uu____15687 ->
                                       let uu____15692 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15692 with
                                        | (t,uu____15704) ->
                                            let uu____15705 = new_uvar r zs t in
                                            (match uu____15705 with
                                             | (k_zs,uu____15717) ->
                                                 let kprob =
                                                   let uu____15719 =
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
                                                          _0_64) uu____15719 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15565 with
                       | (k_u',sub_probs) ->
                           let uu____15736 =
                             let uu____15747 =
                               let uu____15748 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15748 in
                             let uu____15757 =
                               let uu____15760 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15760 in
                             let uu____15763 =
                               let uu____15766 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15766 in
                             (uu____15747, uu____15757, uu____15763) in
                           (match uu____15736 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15785 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15785 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15804 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15804
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15808 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15808 with
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
             let solve_one_pat uu____15861 uu____15862 =
               match (uu____15861, uu____15862) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____15980 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____15980
                     then
                       let uu____15981 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____15982 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____15981 uu____15982
                     else ());
                    (let uu____15984 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____15984
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16003  ->
                              fun uu____16004  ->
                                match (uu____16003, uu____16004) with
                                | ((a,uu____16022),(t21,uu____16024)) ->
                                    let uu____16033 =
                                      let uu____16038 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16038
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16033
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16044 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16044 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16059 = occurs_check env wl (u1, k1) t21 in
                        match uu____16059 with
                        | (occurs_ok,uu____16067) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16075 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16075
                            then
                              let sol =
                                let uu____16077 =
                                  let uu____16086 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16086) in
                                TERM uu____16077 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16093 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16093
                               then
                                 let uu____16094 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16094 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16118,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16144 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16144
                                       then
                                         let uu____16145 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16145
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16152 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16154 = lhs in
             match uu____16154 with
             | (t1,u1,k1,args1) ->
                 let uu____16159 = rhs in
                 (match uu____16159 with
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
                       | uu____16199 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16209 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16209 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16227) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16234 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16234
                                    then
                                      let uu____16235 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16235
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16242 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16244 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16244
        then
          let uu____16245 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16245
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16249 = FStar_Util.physical_equality t1 t2 in
           if uu____16249
           then
             let uu____16250 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16250
           else
             ((let uu____16253 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16253
               then
                 let uu____16254 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16254
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16257,uu____16258) ->
                   let uu____16285 =
                     let uu___337_16286 = problem in
                     let uu____16287 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___337_16286.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16287;
                       FStar_TypeChecker_Common.relation =
                         (uu___337_16286.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___337_16286.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___337_16286.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___337_16286.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___337_16286.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___337_16286.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___337_16286.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___337_16286.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16285 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16288,uu____16289) ->
                   let uu____16296 =
                     let uu___337_16297 = problem in
                     let uu____16298 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___337_16297.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16298;
                       FStar_TypeChecker_Common.relation =
                         (uu___337_16297.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___337_16297.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___337_16297.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___337_16297.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___337_16297.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___337_16297.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___337_16297.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___337_16297.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16296 wl
               | (uu____16299,FStar_Syntax_Syntax.Tm_ascribed uu____16300) ->
                   let uu____16327 =
                     let uu___338_16328 = problem in
                     let uu____16329 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___338_16328.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___338_16328.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___338_16328.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16329;
                       FStar_TypeChecker_Common.element =
                         (uu___338_16328.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___338_16328.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___338_16328.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___338_16328.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___338_16328.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___338_16328.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16327 wl
               | (uu____16330,FStar_Syntax_Syntax.Tm_meta uu____16331) ->
                   let uu____16338 =
                     let uu___338_16339 = problem in
                     let uu____16340 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___338_16339.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___338_16339.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___338_16339.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16340;
                       FStar_TypeChecker_Common.element =
                         (uu___338_16339.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___338_16339.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___338_16339.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___338_16339.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___338_16339.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___338_16339.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16338 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16341,uu____16342) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16343,FStar_Syntax_Syntax.Tm_bvar uu____16344) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___302_16399 =
                     match uu___302_16399 with
                     | [] -> c
                     | bs ->
                         let uu____16421 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16421 in
                   let uu____16430 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16430 with
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
                                   let uu____16572 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16572
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16574 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16574))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___303_16650 =
                     match uu___303_16650 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16684 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16684 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16820 =
                                   let uu____16825 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16826 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16825
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16826 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16820))
               | (FStar_Syntax_Syntax.Tm_abs uu____16831,uu____16832) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____16857 -> true
                     | uu____16874 -> false in
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
                       (let uu____16921 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___339_16929 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___339_16929.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___339_16929.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___339_16929.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___339_16929.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___339_16929.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___339_16929.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___339_16929.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___339_16929.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___339_16929.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___339_16929.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___339_16929.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___339_16929.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___339_16929.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___339_16929.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___339_16929.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___339_16929.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___339_16929.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___339_16929.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___339_16929.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___339_16929.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___339_16929.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___339_16929.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___339_16929.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___339_16929.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___339_16929.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___339_16929.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___339_16929.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___339_16929.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___339_16929.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___339_16929.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___339_16929.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____16921 with
                        | (uu____16932,ty,uu____16934) ->
                            let uu____16935 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____16935) in
                   let uu____16936 =
                     let uu____16953 = maybe_eta t1 in
                     let uu____16960 = maybe_eta t2 in
                     (uu____16953, uu____16960) in
                   (match uu____16936 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___340_17002 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___340_17002.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___340_17002.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___340_17002.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___340_17002.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___340_17002.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___340_17002.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___340_17002.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___340_17002.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17025 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17025
                        then
                          let uu____17026 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17026 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17041 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17041.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17041.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17041.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17041.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17041.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17041.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17041.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17041.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17065 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17065
                        then
                          let uu____17066 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17066 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17081 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17081.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17081.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17081.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17081.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17081.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17081.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17081.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17081.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17085 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17102,FStar_Syntax_Syntax.Tm_abs uu____17103) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17128 -> true
                     | uu____17145 -> false in
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
                       (let uu____17192 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___339_17200 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___339_17200.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___339_17200.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___339_17200.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___339_17200.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___339_17200.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___339_17200.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___339_17200.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___339_17200.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___339_17200.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___339_17200.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___339_17200.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___339_17200.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___339_17200.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___339_17200.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___339_17200.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___339_17200.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___339_17200.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___339_17200.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___339_17200.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___339_17200.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___339_17200.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___339_17200.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___339_17200.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___339_17200.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___339_17200.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___339_17200.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___339_17200.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___339_17200.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___339_17200.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___339_17200.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___339_17200.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17192 with
                        | (uu____17203,ty,uu____17205) ->
                            let uu____17206 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17206) in
                   let uu____17207 =
                     let uu____17224 = maybe_eta t1 in
                     let uu____17231 = maybe_eta t2 in
                     (uu____17224, uu____17231) in
                   (match uu____17207 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___340_17273 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___340_17273.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___340_17273.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___340_17273.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___340_17273.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___340_17273.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___340_17273.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___340_17273.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___340_17273.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17296 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17296
                        then
                          let uu____17297 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17297 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17312 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17312.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17312.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17312.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17312.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17312.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17312.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17312.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17312.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17336 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17336
                        then
                          let uu____17337 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17337 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___341_17352 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___341_17352.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___341_17352.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___341_17352.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___341_17352.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___341_17352.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___341_17352.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___341_17352.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___341_17352.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17356 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17373,FStar_Syntax_Syntax.Tm_refine uu____17374) ->
                   let uu____17387 = as_refinement env wl t1 in
                   (match uu____17387 with
                    | (x1,phi1) ->
                        let uu____17394 = as_refinement env wl t2 in
                        (match uu____17394 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17402 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17402 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17440 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17440
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17444 =
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
                                 let uu____17450 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17450 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17459 =
                                   let uu____17464 =
                                     let uu____17465 =
                                       let uu____17472 =
                                         FStar_Syntax_Syntax.mk_binder x11 in
                                       [uu____17472] in
                                     FStar_List.append (p_scope orig)
                                       uu____17465 in
                                   mk_problem uu____17464 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17459 in
                               let uu____17481 =
                                 solve env1
                                   (let uu___342_17483 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___342_17483.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___342_17483.smt_ok);
                                      tcenv = (uu___342_17483.tcenv)
                                    }) in
                               (match uu____17481 with
                                | Failed uu____17490 -> fallback ()
                                | Success uu____17495 ->
                                    let guard =
                                      let uu____17499 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17504 =
                                        let uu____17505 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17505
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17499
                                        uu____17504 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___343_17514 = wl1 in
                                      {
                                        attempting =
                                          (uu___343_17514.attempting);
                                        wl_deferred =
                                          (uu___343_17514.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___343_17514.defer_ok);
                                        smt_ok = (uu___343_17514.smt_ok);
                                        tcenv = (uu___343_17514.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17516,FStar_Syntax_Syntax.Tm_uvar uu____17517) ->
                   let uu____17550 = destruct_flex_t t1 in
                   let uu____17551 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17550 uu____17551
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17552;
                     FStar_Syntax_Syntax.pos = uu____17553;
                     FStar_Syntax_Syntax.vars = uu____17554;_},uu____17555),FStar_Syntax_Syntax.Tm_uvar
                  uu____17556) ->
                   let uu____17609 = destruct_flex_t t1 in
                   let uu____17610 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17609 uu____17610
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17611,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17612;
                     FStar_Syntax_Syntax.pos = uu____17613;
                     FStar_Syntax_Syntax.vars = uu____17614;_},uu____17615))
                   ->
                   let uu____17668 = destruct_flex_t t1 in
                   let uu____17669 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17668 uu____17669
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17670;
                     FStar_Syntax_Syntax.pos = uu____17671;
                     FStar_Syntax_Syntax.vars = uu____17672;_},uu____17673),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17674;
                     FStar_Syntax_Syntax.pos = uu____17675;
                     FStar_Syntax_Syntax.vars = uu____17676;_},uu____17677))
                   ->
                   let uu____17750 = destruct_flex_t t1 in
                   let uu____17751 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17750 uu____17751
               | (FStar_Syntax_Syntax.Tm_uvar uu____17752,uu____17753) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17770 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17770 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17777;
                     FStar_Syntax_Syntax.pos = uu____17778;
                     FStar_Syntax_Syntax.vars = uu____17779;_},uu____17780),uu____17781)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17818 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17818 t2 wl
               | (uu____17825,FStar_Syntax_Syntax.Tm_uvar uu____17826) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____17843,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17844;
                     FStar_Syntax_Syntax.pos = uu____17845;
                     FStar_Syntax_Syntax.vars = uu____17846;_},uu____17847))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17884,FStar_Syntax_Syntax.Tm_type uu____17885) ->
                   solve_t' env
                     (let uu___344_17903 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_17903.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_17903.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_17903.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_17903.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_17903.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_17903.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_17903.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_17903.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_17903.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17904;
                     FStar_Syntax_Syntax.pos = uu____17905;
                     FStar_Syntax_Syntax.vars = uu____17906;_},uu____17907),FStar_Syntax_Syntax.Tm_type
                  uu____17908) ->
                   solve_t' env
                     (let uu___344_17946 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_17946.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_17946.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_17946.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_17946.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_17946.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_17946.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_17946.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_17946.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_17946.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17947,FStar_Syntax_Syntax.Tm_arrow uu____17948) ->
                   solve_t' env
                     (let uu___344_17978 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_17978.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_17978.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_17978.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_17978.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_17978.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_17978.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_17978.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_17978.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_17978.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17979;
                     FStar_Syntax_Syntax.pos = uu____17980;
                     FStar_Syntax_Syntax.vars = uu____17981;_},uu____17982),FStar_Syntax_Syntax.Tm_arrow
                  uu____17983) ->
                   solve_t' env
                     (let uu___344_18033 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___344_18033.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___344_18033.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___344_18033.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___344_18033.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___344_18033.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___344_18033.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___344_18033.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___344_18033.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___344_18033.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18034,uu____18035) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18054 =
                        let uu____18055 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18055 in
                      if uu____18054
                      then
                        let uu____18056 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___345_18062 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___345_18062.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___345_18062.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___345_18062.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___345_18062.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___345_18062.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___345_18062.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___345_18062.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___345_18062.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___345_18062.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18063 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18056 uu____18063 t2
                          wl
                      else
                        (let uu____18071 = base_and_refinement env t2 in
                         match uu____18071 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18100 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___346_18106 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___346_18106.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___346_18106.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___346_18106.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___346_18106.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___346_18106.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___346_18106.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___346_18106.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___346_18106.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___346_18106.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18107 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18100
                                    uu____18107 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___347_18121 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___347_18121.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___347_18121.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18124 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18124 in
                                  let guard =
                                    let uu____18136 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18136
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18144;
                     FStar_Syntax_Syntax.pos = uu____18145;
                     FStar_Syntax_Syntax.vars = uu____18146;_},uu____18147),uu____18148)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18187 =
                        let uu____18188 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18188 in
                      if uu____18187
                      then
                        let uu____18189 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___345_18195 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___345_18195.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___345_18195.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___345_18195.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___345_18195.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___345_18195.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___345_18195.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___345_18195.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___345_18195.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___345_18195.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18196 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18189 uu____18196 t2
                          wl
                      else
                        (let uu____18204 = base_and_refinement env t2 in
                         match uu____18204 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18233 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___346_18239 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___346_18239.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___346_18239.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___346_18239.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___346_18239.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___346_18239.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___346_18239.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___346_18239.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___346_18239.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___346_18239.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18240 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18233
                                    uu____18240 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___347_18254 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___347_18254.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___347_18254.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18257 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18257 in
                                  let guard =
                                    let uu____18269 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18269
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18277,FStar_Syntax_Syntax.Tm_uvar uu____18278) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18296 = base_and_refinement env t1 in
                      match uu____18296 with
                      | (t_base,uu____18308) ->
                          solve_t env
                            (let uu___348_18322 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___348_18322.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___348_18322.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___348_18322.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___348_18322.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___348_18322.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___348_18322.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___348_18322.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___348_18322.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18323,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18324;
                     FStar_Syntax_Syntax.pos = uu____18325;
                     FStar_Syntax_Syntax.vars = uu____18326;_},uu____18327))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18365 = base_and_refinement env t1 in
                      match uu____18365 with
                      | (t_base,uu____18377) ->
                          solve_t env
                            (let uu___348_18391 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___348_18391.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___348_18391.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___348_18391.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___348_18391.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___348_18391.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___348_18391.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___348_18391.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___348_18391.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18392,uu____18393) ->
                   let t21 =
                     let uu____18403 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18403 in
                   solve_t env
                     (let uu___349_18427 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___349_18427.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___349_18427.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___349_18427.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___349_18427.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___349_18427.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___349_18427.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___349_18427.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___349_18427.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___349_18427.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18428,FStar_Syntax_Syntax.Tm_refine uu____18429) ->
                   let t11 =
                     let uu____18439 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18439 in
                   solve_t env
                     (let uu___350_18463 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___350_18463.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___350_18463.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___350_18463.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___350_18463.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___350_18463.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___350_18463.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___350_18463.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___350_18463.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___350_18463.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18466,uu____18467) ->
                   let head1 =
                     let uu____18493 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18493
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18537 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18537
                       FStar_Pervasives_Native.fst in
                   let uu____18578 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18578
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18593 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18593
                      then
                        let guard =
                          let uu____18605 =
                            let uu____18606 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18606 = FStar_Syntax_Util.Equal in
                          if uu____18605
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18610 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18610) in
                        let uu____18613 = solve_prob orig guard [] wl in
                        solve env uu____18613
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18616,uu____18617) ->
                   let head1 =
                     let uu____18627 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18627
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18671 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18671
                       FStar_Pervasives_Native.fst in
                   let uu____18712 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18712
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18727 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18727
                      then
                        let guard =
                          let uu____18739 =
                            let uu____18740 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18740 = FStar_Syntax_Util.Equal in
                          if uu____18739
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18744 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18744) in
                        let uu____18747 = solve_prob orig guard [] wl in
                        solve env uu____18747
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18750,uu____18751) ->
                   let head1 =
                     let uu____18755 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18755
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18799 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18799
                       FStar_Pervasives_Native.fst in
                   let uu____18840 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18840
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18855 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18855
                      then
                        let guard =
                          let uu____18867 =
                            let uu____18868 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18868 = FStar_Syntax_Util.Equal in
                          if uu____18867
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18872 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____18872) in
                        let uu____18875 = solve_prob orig guard [] wl in
                        solve env uu____18875
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____18878,uu____18879) ->
                   let head1 =
                     let uu____18883 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18883
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18927 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18927
                       FStar_Pervasives_Native.fst in
                   let uu____18968 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18968
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18983 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18983
                      then
                        let guard =
                          let uu____18995 =
                            let uu____18996 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18996 = FStar_Syntax_Util.Equal in
                          if uu____18995
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19000 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19000) in
                        let uu____19003 = solve_prob orig guard [] wl in
                        solve env uu____19003
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19006,uu____19007) ->
                   let head1 =
                     let uu____19011 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19011
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19055 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19055
                       FStar_Pervasives_Native.fst in
                   let uu____19096 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19096
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19111 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19111
                      then
                        let guard =
                          let uu____19123 =
                            let uu____19124 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19124 = FStar_Syntax_Util.Equal in
                          if uu____19123
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19128 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19128) in
                        let uu____19131 = solve_prob orig guard [] wl in
                        solve env uu____19131
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19134,uu____19135) ->
                   let head1 =
                     let uu____19153 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19153
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19197 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19197
                       FStar_Pervasives_Native.fst in
                   let uu____19238 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19238
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19253 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19253
                      then
                        let guard =
                          let uu____19265 =
                            let uu____19266 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19266 = FStar_Syntax_Util.Equal in
                          if uu____19265
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19270 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19270) in
                        let uu____19273 = solve_prob orig guard [] wl in
                        solve env uu____19273
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19276,FStar_Syntax_Syntax.Tm_match uu____19277) ->
                   let head1 =
                     let uu____19303 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19303
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19347 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19347
                       FStar_Pervasives_Native.fst in
                   let uu____19388 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19388
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19403 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19403
                      then
                        let guard =
                          let uu____19415 =
                            let uu____19416 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19416 = FStar_Syntax_Util.Equal in
                          if uu____19415
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19420 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19420) in
                        let uu____19423 = solve_prob orig guard [] wl in
                        solve env uu____19423
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19426,FStar_Syntax_Syntax.Tm_uinst uu____19427) ->
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
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19554) in
                        let uu____19557 = solve_prob orig guard [] wl in
                        solve env uu____19557
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19560,FStar_Syntax_Syntax.Tm_name uu____19561) ->
                   let head1 =
                     let uu____19565 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19565
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19609 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19609
                       FStar_Pervasives_Native.fst in
                   let uu____19650 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19650
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19665 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19665
                      then
                        let guard =
                          let uu____19677 =
                            let uu____19678 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19678 = FStar_Syntax_Util.Equal in
                          if uu____19677
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19682 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19682) in
                        let uu____19685 = solve_prob orig guard [] wl in
                        solve env uu____19685
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19688,FStar_Syntax_Syntax.Tm_constant uu____19689) ->
                   let head1 =
                     let uu____19693 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19693
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19737 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19737
                       FStar_Pervasives_Native.fst in
                   let uu____19778 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19778
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19793 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19793
                      then
                        let guard =
                          let uu____19805 =
                            let uu____19806 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19806 = FStar_Syntax_Util.Equal in
                          if uu____19805
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19810 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19810) in
                        let uu____19813 = solve_prob orig guard [] wl in
                        solve env uu____19813
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19816,FStar_Syntax_Syntax.Tm_fvar uu____19817) ->
                   let head1 =
                     let uu____19821 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19821
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19865 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19865
                       FStar_Pervasives_Native.fst in
                   let uu____19906 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19906
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19921 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19921
                      then
                        let guard =
                          let uu____19933 =
                            let uu____19934 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19934 = FStar_Syntax_Util.Equal in
                          if uu____19933
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19938 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____19938) in
                        let uu____19941 = solve_prob orig guard [] wl in
                        solve env uu____19941
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19944,FStar_Syntax_Syntax.Tm_app uu____19945) ->
                   let head1 =
                     let uu____19963 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19963
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20007 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20007
                       FStar_Pervasives_Native.fst in
                   let uu____20048 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20048
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20063 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20063
                      then
                        let guard =
                          let uu____20075 =
                            let uu____20076 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20076 = FStar_Syntax_Util.Equal in
                          if uu____20075
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20080 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20080) in
                        let uu____20083 = solve_prob orig guard [] wl in
                        solve env uu____20083
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20086,uu____20087) ->
                   let uu____20100 =
                     let uu____20101 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20102 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20101
                       uu____20102 in
                   failwith uu____20100
               | (FStar_Syntax_Syntax.Tm_delayed uu____20103,uu____20104) ->
                   let uu____20129 =
                     let uu____20130 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20131 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20130
                       uu____20131 in
                   failwith uu____20129
               | (uu____20132,FStar_Syntax_Syntax.Tm_delayed uu____20133) ->
                   let uu____20158 =
                     let uu____20159 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20160 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20159
                       uu____20160 in
                   failwith uu____20158
               | (uu____20161,FStar_Syntax_Syntax.Tm_let uu____20162) ->
                   let uu____20175 =
                     let uu____20176 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20177 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20176
                       uu____20177 in
                   failwith uu____20175
               | uu____20178 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20214 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20214
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20216 =
               let uu____20217 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20218 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20217 uu____20218 in
             giveup env uu____20216 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20238  ->
                    fun uu____20239  ->
                      match (uu____20238, uu____20239) with
                      | ((a1,uu____20257),(a2,uu____20259)) ->
                          let uu____20268 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20268)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20278 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20278 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20302 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20309)::[] -> wp1
              | uu____20326 ->
                  let uu____20335 =
                    let uu____20336 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20336 in
                  failwith uu____20335 in
            let uu____20339 =
              let uu____20348 =
                let uu____20349 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20349 in
              [uu____20348] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20339;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20350 = lift_c1 () in solve_eq uu____20350 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___304_20356  ->
                       match uu___304_20356 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20357 -> false)) in
             let uu____20358 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20392)::uu____20393,(wp2,uu____20395)::uu____20396)
                   -> (wp1, wp2)
               | uu____20453 ->
                   let uu____20474 =
                     let uu____20475 =
                       let uu____20480 =
                         let uu____20481 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20482 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20481 uu____20482 in
                       (uu____20480, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20475 in
                   FStar_Exn.raise uu____20474 in
             match uu____20358 with
             | (wpc1,wpc2) ->
                 let uu____20501 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20501
                 then
                   let uu____20504 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20504 wl
                 else
                   (let uu____20508 =
                      let uu____20515 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20515 in
                    match uu____20508 with
                    | (c2_decl,qualifiers) ->
                        let uu____20536 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20536
                        then
                          let c1_repr =
                            let uu____20540 =
                              let uu____20541 =
                                let uu____20542 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20542 in
                              let uu____20543 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20541 uu____20543 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20540 in
                          let c2_repr =
                            let uu____20545 =
                              let uu____20546 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20547 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20546 uu____20547 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20545 in
                          let prob =
                            let uu____20549 =
                              let uu____20554 =
                                let uu____20555 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20556 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20555
                                  uu____20556 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20554 in
                            FStar_TypeChecker_Common.TProb uu____20549 in
                          let wl1 =
                            let uu____20558 =
                              let uu____20561 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20561 in
                            solve_prob orig uu____20558 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20570 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20570
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____20572 =
                                     let uu____20575 =
                                       let uu____20576 =
                                         let uu____20591 =
                                           let uu____20592 =
                                             let uu____20593 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____20593] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____20592 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20594 =
                                           let uu____20597 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20598 =
                                             let uu____20601 =
                                               let uu____20602 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20602 in
                                             [uu____20601] in
                                           uu____20597 :: uu____20598 in
                                         (uu____20591, uu____20594) in
                                       FStar_Syntax_Syntax.Tm_app uu____20576 in
                                     FStar_Syntax_Syntax.mk uu____20575 in
                                   uu____20572 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____20609 =
                                    let uu____20612 =
                                      let uu____20613 =
                                        let uu____20628 =
                                          let uu____20629 =
                                            let uu____20630 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____20630] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____20629 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20631 =
                                          let uu____20634 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20635 =
                                            let uu____20638 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20639 =
                                              let uu____20642 =
                                                let uu____20643 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20643 in
                                              [uu____20642] in
                                            uu____20638 :: uu____20639 in
                                          uu____20634 :: uu____20635 in
                                        (uu____20628, uu____20631) in
                                      FStar_Syntax_Syntax.Tm_app uu____20613 in
                                    FStar_Syntax_Syntax.mk uu____20612 in
                                  uu____20609 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20650 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20650 in
                           let wl1 =
                             let uu____20660 =
                               let uu____20663 =
                                 let uu____20666 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20666 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20663 in
                             solve_prob orig uu____20660 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20679 = FStar_Util.physical_equality c1 c2 in
        if uu____20679
        then
          let uu____20680 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20680
        else
          ((let uu____20683 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20683
            then
              let uu____20684 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20685 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20684
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20685
            else ());
           (let uu____20687 =
              let uu____20692 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20693 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20692, uu____20693) in
            match uu____20687 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20697),FStar_Syntax_Syntax.Total
                    (t2,uu____20699)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20716 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20716 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20719,FStar_Syntax_Syntax.Total uu____20720) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20738),FStar_Syntax_Syntax.Total
                    (t2,uu____20740)) ->
                     let uu____20757 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20757 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20761),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20763)) ->
                     let uu____20780 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20780 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20784),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20786)) ->
                     let uu____20803 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20803 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20806,FStar_Syntax_Syntax.Comp uu____20807) ->
                     let uu____20816 =
                       let uu___351_20821 = problem in
                       let uu____20826 =
                         let uu____20827 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20827 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___351_20821.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20826;
                         FStar_TypeChecker_Common.relation =
                           (uu___351_20821.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___351_20821.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___351_20821.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___351_20821.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___351_20821.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___351_20821.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___351_20821.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___351_20821.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20816 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20828,FStar_Syntax_Syntax.Comp uu____20829) ->
                     let uu____20838 =
                       let uu___351_20843 = problem in
                       let uu____20848 =
                         let uu____20849 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20849 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___351_20843.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20848;
                         FStar_TypeChecker_Common.relation =
                           (uu___351_20843.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___351_20843.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___351_20843.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___351_20843.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___351_20843.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___351_20843.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___351_20843.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___351_20843.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20838 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20850,FStar_Syntax_Syntax.GTotal uu____20851) ->
                     let uu____20860 =
                       let uu___352_20865 = problem in
                       let uu____20870 =
                         let uu____20871 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20871 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___352_20865.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___352_20865.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___352_20865.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20870;
                         FStar_TypeChecker_Common.element =
                           (uu___352_20865.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___352_20865.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___352_20865.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___352_20865.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___352_20865.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___352_20865.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20860 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20872,FStar_Syntax_Syntax.Total uu____20873) ->
                     let uu____20882 =
                       let uu___352_20887 = problem in
                       let uu____20892 =
                         let uu____20893 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20893 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___352_20887.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___352_20887.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___352_20887.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20892;
                         FStar_TypeChecker_Common.element =
                           (uu___352_20887.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___352_20887.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___352_20887.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___352_20887.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___352_20887.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___352_20887.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20882 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20894,FStar_Syntax_Syntax.Comp uu____20895) ->
                     let uu____20896 =
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
                     if uu____20896
                     then
                       let uu____20897 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____20897 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20903 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20913 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____20914 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____20913, uu____20914)) in
                          match uu____20903 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____20921 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____20921
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20923 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____20923 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20926 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____20928 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____20928) in
                                if uu____20926
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
                                  (let uu____20931 =
                                     let uu____20932 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____20933 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____20932 uu____20933 in
                                   giveup env uu____20931 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____20938 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20976  ->
              match uu____20976 with
              | (uu____20989,uu____20990,u,uu____20992,uu____20993,uu____20994)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____20938 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21025 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21025 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21043 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21071  ->
                match uu____21071 with
                | (u1,u2) ->
                    let uu____21078 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21079 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21078 uu____21079)) in
      FStar_All.pipe_right uu____21043 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21096,[])) -> "{}"
      | uu____21121 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21138 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21138
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21141 =
              FStar_List.map
                (fun uu____21151  ->
                   match uu____21151 with
                   | (uu____21156,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21141 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21161 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21161 imps
let new_t_problem:
  'Auu____21169 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21169 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21169)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21203 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21203
                then
                  let uu____21204 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21205 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21204
                    (rel_to_string rel) uu____21205
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
            let uu____21229 =
              let uu____21232 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21232 in
            FStar_Syntax_Syntax.new_bv uu____21229 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21241 =
              let uu____21244 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21244 in
            let uu____21247 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21241 uu____21247 in
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
          let uu____21277 = FStar_Options.eager_inference () in
          if uu____21277
          then
            let uu___353_21278 = probs in
            {
              attempting = (uu___353_21278.attempting);
              wl_deferred = (uu___353_21278.wl_deferred);
              ctr = (uu___353_21278.ctr);
              defer_ok = false;
              smt_ok = (uu___353_21278.smt_ok);
              tcenv = (uu___353_21278.tcenv)
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
             (let uu____21290 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21290
              then
                let uu____21291 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21291
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
          ((let uu____21301 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21301
            then
              let uu____21302 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21302
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21306 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21306
             then
               let uu____21307 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21307
             else ());
            (let f2 =
               let uu____21310 =
                 let uu____21311 = FStar_Syntax_Util.unmeta f1 in
                 uu____21311.FStar_Syntax_Syntax.n in
               match uu____21310 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21315 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___354_21316 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___354_21316.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___354_21316.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___354_21316.FStar_TypeChecker_Env.implicits)
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
            let uu____21335 =
              let uu____21336 =
                let uu____21337 =
                  let uu____21338 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21338
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21337;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21336 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21335
let with_guard_no_simp:
  'Auu____21365 .
    'Auu____21365 ->
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
            let uu____21385 =
              let uu____21386 =
                let uu____21387 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21387
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21386;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21385
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
          (let uu____21425 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21425
           then
             let uu____21426 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21427 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21426
               uu____21427
           else ());
          (let prob =
             let uu____21430 =
               let uu____21435 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21435 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21430 in
           let g =
             let uu____21443 =
               let uu____21446 = singleton' env prob smt_ok in
               solve_and_commit env uu____21446
                 (fun uu____21448  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21443 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21466 = try_teq true env t1 t2 in
        match uu____21466 with
        | FStar_Pervasives_Native.None  ->
            let uu____21469 =
              let uu____21470 =
                let uu____21475 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21476 = FStar_TypeChecker_Env.get_range env in
                (uu____21475, uu____21476) in
              FStar_Errors.Error uu____21470 in
            FStar_Exn.raise uu____21469
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21479 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21479
              then
                let uu____21480 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21481 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21482 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21480
                  uu____21481 uu____21482
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
          (let uu____21499 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21499
           then
             let uu____21500 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21501 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21500
               uu____21501
           else ());
          (let uu____21503 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21503 with
           | (prob,x) ->
               let g =
                 let uu____21515 =
                   let uu____21518 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21518
                     (fun uu____21520  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21515 in
               ((let uu____21530 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____21530
                 then
                   let uu____21531 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____21532 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____21533 =
                     let uu____21534 = FStar_Util.must g in
                     guard_to_string env uu____21534 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____21531 uu____21532 uu____21533
                 else ());
                (let uu____21536 =
                   let uu____21539 = FStar_Syntax_Syntax.mk_binder x in
                   abstract_guard uu____21539 in
                 FStar_Util.map_opt g uu____21536)))
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
          let uu____21563 = FStar_TypeChecker_Env.get_range env in
          let uu____21564 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21563 uu____21564
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21577 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21577
         then
           let uu____21578 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21579 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21578
             uu____21579
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21584 =
             let uu____21589 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21589 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21584 in
         let uu____21594 =
           let uu____21597 = singleton env prob in
           solve_and_commit env uu____21597
             (fun uu____21599  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21594)
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
      fun uu____21628  ->
        match uu____21628 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21667 =
                 let uu____21668 =
                   let uu____21673 =
                     let uu____21674 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21675 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21674 uu____21675 in
                   let uu____21676 = FStar_TypeChecker_Env.get_range env in
                   (uu____21673, uu____21676) in
                 FStar_Errors.Error uu____21668 in
               FStar_Exn.raise uu____21667) in
            let equiv1 v1 v' =
              let uu____21684 =
                let uu____21689 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21690 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21689, uu____21690) in
              match uu____21684 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21709 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21739 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21739 with
                      | FStar_Syntax_Syntax.U_unif uu____21746 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21775  ->
                                    match uu____21775 with
                                    | (u,v') ->
                                        let uu____21784 = equiv1 v1 v' in
                                        if uu____21784
                                        then
                                          let uu____21787 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21787 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21803 -> [])) in
            let uu____21808 =
              let wl =
                let uu___355_21812 = empty_worklist env in
                {
                  attempting = (uu___355_21812.attempting);
                  wl_deferred = (uu___355_21812.wl_deferred);
                  ctr = (uu___355_21812.ctr);
                  defer_ok = false;
                  smt_ok = (uu___355_21812.smt_ok);
                  tcenv = (uu___355_21812.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21830  ->
                      match uu____21830 with
                      | (lb,v1) ->
                          let uu____21837 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21837 with
                           | USolved wl1 -> ()
                           | uu____21839 -> fail lb v1))) in
            let rec check_ineq uu____21847 =
              match uu____21847 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21856) -> true
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
                      uu____21879,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21881,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21892) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21899,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21907 -> false) in
            let uu____21912 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21927  ->
                      match uu____21927 with
                      | (u,v1) ->
                          let uu____21934 = check_ineq (u, v1) in
                          if uu____21934
                          then true
                          else
                            ((let uu____21937 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____21937
                              then
                                let uu____21938 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____21939 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____21938
                                  uu____21939
                              else ());
                             false))) in
            if uu____21912
            then ()
            else
              ((let uu____21943 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____21943
                then
                  ((let uu____21945 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21945);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21955 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21955))
                else ());
               (let uu____21965 =
                  let uu____21966 =
                    let uu____21971 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____21971) in
                  FStar_Errors.Error uu____21966 in
                FStar_Exn.raise uu____21965))
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
      let fail uu____22019 =
        match uu____22019 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22033 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22033
       then
         let uu____22034 = wl_to_string wl in
         let uu____22035 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22034 uu____22035
       else ());
      (let g1 =
         let uu____22050 = solve_and_commit env wl fail in
         match uu____22050 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___356_22063 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___356_22063.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___356_22063.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___356_22063.FStar_TypeChecker_Env.implicits)
             }
         | uu____22068 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___357_22072 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___357_22072.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___357_22072.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___357_22072.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22094 = FStar_ST.op_Bang last_proof_ns in
    match uu____22094 with
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
            let uu___358_22278 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___358_22278.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___358_22278.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___358_22278.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22279 =
            let uu____22280 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22280 in
          if uu____22279
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22288 = FStar_TypeChecker_Env.get_range env in
                     let uu____22289 =
                       let uu____22290 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22290 in
                     FStar_Errors.diag uu____22288 uu____22289)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22294 = FStar_TypeChecker_Env.get_range env in
                      let uu____22295 =
                        let uu____22296 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22296 in
                      FStar_Errors.diag uu____22294 uu____22295)
                   else ();
                   (let uu____22298 = check_trivial vc1 in
                    match uu____22298 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22305 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22306 =
                                let uu____22307 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22307 in
                              FStar_Errors.diag uu____22305 uu____22306)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22312 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22313 =
                                let uu____22314 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22314 in
                              FStar_Errors.diag uu____22312 uu____22313)
                           else ();
                           (let vcs =
                              let uu____22325 = FStar_Options.use_tactics () in
                              if uu____22325
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22344  ->
                                     (let uu____22346 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22346);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22348 =
                                   let uu____22355 = FStar_Options.peek () in
                                   (env, vc2, uu____22355) in
                                 [uu____22348]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22389  ->
                                    match uu____22389 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22400 = check_trivial goal1 in
                                        (match uu____22400 with
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
                                                (let uu____22408 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22409 =
                                                   let uu____22410 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22411 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22410 uu____22411 in
                                                 FStar_Errors.diag
                                                   uu____22408 uu____22409)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22414 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22415 =
                                                   let uu____22416 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22416 in
                                                 FStar_Errors.diag
                                                   uu____22414 uu____22415)
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
      let uu____22426 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22426 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22432 =
            let uu____22433 =
              let uu____22438 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22438) in
            FStar_Errors.Error uu____22433 in
          FStar_Exn.raise uu____22432
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22445 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22445 with
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
          let uu____22464 = FStar_Syntax_Unionfind.find u in
          match uu____22464 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22467 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22485 = acc in
          match uu____22485 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22571 = hd1 in
                   (match uu____22571 with
                    | (uu____22584,env,u,tm,k,r) ->
                        let uu____22590 = unresolved u in
                        if uu____22590
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22621 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22621
                            then
                              let uu____22622 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22623 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22624 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22622 uu____22623 uu____22624
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___359_22627 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___359_22627.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___359_22627.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___359_22627.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___359_22627.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___359_22627.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___359_22627.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___359_22627.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___359_22627.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___359_22627.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___359_22627.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___359_22627.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___359_22627.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___359_22627.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___359_22627.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___359_22627.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___359_22627.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___359_22627.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___359_22627.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___359_22627.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___359_22627.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___359_22627.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___359_22627.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___359_22627.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___359_22627.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___359_22627.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___359_22627.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___359_22627.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___359_22627.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___359_22627.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___359_22627.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___359_22627.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___359_22627.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___359_22627.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____22630 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___360_22638 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___360_22638.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___360_22638.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___360_22638.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___360_22638.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___360_22638.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___360_22638.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___360_22638.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___360_22638.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___360_22638.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___360_22638.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___360_22638.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___360_22638.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___360_22638.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___360_22638.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___360_22638.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___360_22638.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___360_22638.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___360_22638.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___360_22638.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___360_22638.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___360_22638.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___360_22638.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___360_22638.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___360_22638.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___360_22638.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___360_22638.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___360_22638.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___360_22638.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___360_22638.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___360_22638.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___360_22638.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___360_22638.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.dep_graph =
                                         (uu___360_22638.FStar_TypeChecker_Env.dep_graph)
                                     }) tm1 in
                                match uu____22630 with
                                | (uu____22639,uu____22640,g1) -> g1
                              else
                                (let uu____22643 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___361_22651 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___361_22651.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___361_22651.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___361_22651.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___361_22651.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___361_22651.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___361_22651.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___361_22651.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___361_22651.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___361_22651.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___361_22651.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___361_22651.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___361_22651.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___361_22651.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___361_22651.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___361_22651.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___361_22651.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___361_22651.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___361_22651.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___361_22651.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___361_22651.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___361_22651.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___361_22651.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___361_22651.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___361_22651.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___361_22651.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___361_22651.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___361_22651.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___361_22651.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___361_22651.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___361_22651.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___361_22651.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___361_22651.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___361_22651.FStar_TypeChecker_Env.dep_graph)
                                      }) tm1 in
                                 match uu____22643 with
                                 | (uu____22652,uu____22653,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___362_22656 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___362_22656.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___362_22656.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___362_22656.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____22659 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____22665  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____22659 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___363_22693 = g in
        let uu____22694 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___363_22693.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___363_22693.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___363_22693.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____22694
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
        let uu____22748 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22748 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22761 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22761
      | (reason,uu____22763,uu____22764,e,t,r)::uu____22768 ->
          let uu____22795 =
            let uu____22796 =
              let uu____22801 =
                let uu____22802 = FStar_Syntax_Print.term_to_string t in
                let uu____22803 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22802 uu____22803 in
              (uu____22801, r) in
            FStar_Errors.Error uu____22796 in
          FStar_Exn.raise uu____22795
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___364_22810 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___364_22810.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___364_22810.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___364_22810.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22836 = try_teq false env t1 t2 in
        match uu____22836 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____22840 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____22840 with
             | FStar_Pervasives_Native.Some uu____22845 -> true
             | FStar_Pervasives_Native.None  -> false)