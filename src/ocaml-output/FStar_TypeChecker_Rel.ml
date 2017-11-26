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
          let uu___246_91 = g in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___246_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___246_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___246_91.FStar_TypeChecker_Env.implicits)
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
          let uu___247_175 = g in
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
              (uu___247_175.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___247_175.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___247_175.FStar_TypeChecker_Env.implicits)
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
          let uu___248_218 = g in
          let uu____219 =
            let uu____220 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____220 in
          {
            FStar_TypeChecker_Env.guard_f = uu____219;
            FStar_TypeChecker_Env.deferred =
              (uu___248_218.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___248_218.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___248_218.FStar_TypeChecker_Env.implicits)
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
            let uu___249_344 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___249_344.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___249_344.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___249_344.FStar_TypeChecker_Env.implicits)
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
            let uu___250_376 = g in
            let uu____377 =
              let uu____378 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____378 in
            {
              FStar_TypeChecker_Env.guard_f = uu____377;
              FStar_TypeChecker_Env.deferred =
                (uu___250_376.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___250_376.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___250_376.FStar_TypeChecker_Env.implicits)
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
  fun uu___217_812  ->
    match uu___217_812 with
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
    fun uu___218_909  ->
      match uu___218_909 with
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
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____936 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____937 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____935 uu____936
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____937
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___219_943  ->
      match uu___219_943 with
      | UNIV (u,t) ->
          let x =
            let uu____947 = FStar_Options.hide_uvar_nums () in
            if uu____947
            then "?"
            else
              (let uu____949 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____949 FStar_Util.string_of_int) in
          let uu____950 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____950
      | TERM ((u,uu____952),t) ->
          let x =
            let uu____959 = FStar_Options.hide_uvar_nums () in
            if uu____959
            then "?"
            else
              (let uu____961 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____961 FStar_Util.string_of_int) in
          let uu____962 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____962
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____973 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____973 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____985 =
      let uu____988 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____988
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____985 (FStar_String.concat ", ")
let args_to_string:
  'Auu____999 .
    (FStar_Syntax_Syntax.term,'Auu____999) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1016 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1034  ->
              match uu____1034 with
              | (x,uu____1040) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1016 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1046 =
      let uu____1047 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1047 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1046;
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
        let uu___251_1063 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___251_1063.wl_deferred);
          ctr = (uu___251_1063.ctr);
          defer_ok = (uu___251_1063.defer_ok);
          smt_ok;
          tcenv = (uu___251_1063.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1073 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1073,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___252_1094 = empty_worklist env in
      let uu____1095 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1095;
        wl_deferred = (uu___252_1094.wl_deferred);
        ctr = (uu___252_1094.ctr);
        defer_ok = false;
        smt_ok = (uu___252_1094.smt_ok);
        tcenv = (uu___252_1094.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___253_1109 = wl in
        {
          attempting = (uu___253_1109.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___253_1109.ctr);
          defer_ok = (uu___253_1109.defer_ok);
          smt_ok = (uu___253_1109.smt_ok);
          tcenv = (uu___253_1109.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___254_1126 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___254_1126.wl_deferred);
        ctr = (uu___254_1126.ctr);
        defer_ok = (uu___254_1126.defer_ok);
        smt_ok = (uu___254_1126.smt_ok);
        tcenv = (uu___254_1126.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1137 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1137
         then
           let uu____1138 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1138
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___220_1142  ->
    match uu___220_1142 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1146 'Auu____1147 .
    ('Auu____1147,'Auu____1146) FStar_TypeChecker_Common.problem ->
      ('Auu____1147,'Auu____1146) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___255_1164 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___255_1164.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___255_1164.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___255_1164.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___255_1164.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___255_1164.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___255_1164.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___255_1164.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1172 'Auu____1173 .
    ('Auu____1173,'Auu____1172) FStar_TypeChecker_Common.problem ->
      ('Auu____1173,'Auu____1172) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___221_1193  ->
    match uu___221_1193 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___222_1217  ->
      match uu___222_1217 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___223_1220  ->
    match uu___223_1220 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___224_1233  ->
    match uu___224_1233 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___225_1248  ->
    match uu___225_1248 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___226_1263  ->
    match uu___226_1263 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___227_1280  ->
    match uu___227_1280 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___228_1297  ->
    match uu___228_1297 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___229_1310  ->
    match uu___229_1310 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1332 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1332 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1344  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1436 'Auu____1437 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1437 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1437 ->
              'Auu____1436 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1437,'Auu____1436)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1474 = next_pid () in
                let uu____1475 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1474;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1475;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1489 'Auu____1490 .
    FStar_TypeChecker_Env.env ->
      'Auu____1490 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1490 ->
            'Auu____1489 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1490,'Auu____1489)
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
                let uu____1528 = next_pid () in
                let uu____1529 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1528;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1529;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1542 'Auu____1543 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1543 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1543 ->
            'Auu____1542 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1543,'Auu____1542) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1576 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1576;
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
  'Auu____1582 .
    worklist ->
      ('Auu____1582,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1632 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1632
        then
          let uu____1633 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1634 = prob_to_string env d in
          let uu____1635 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1633 uu____1634 uu____1635 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1641 -> failwith "impossible" in
           let uu____1642 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1656 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1657 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1656, uu____1657)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1663 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1664 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1663, uu____1664) in
           match uu____1642 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___230_1680  ->
            match uu___230_1680 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1692 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1694),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___231_1714  ->
           match uu___231_1714 with
           | UNIV uu____1717 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1723),t) ->
               let uu____1729 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1729
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
        (fun uu___232_1749  ->
           match uu___232_1749 with
           | UNIV (u',t) ->
               let uu____1754 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1754
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1758 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1765 =
        let uu____1766 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1766 in
      FStar_Syntax_Subst.compress uu____1765
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1773 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1773
let norm_arg:
  'Auu____1777 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1777) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1777)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1798 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1798, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1829  ->
              match uu____1829 with
              | (x,imp) ->
                  let uu____1840 =
                    let uu___256_1841 = x in
                    let uu____1842 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___256_1841.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___256_1841.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1842
                    } in
                  (uu____1840, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1857 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1857
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1861 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1861
        | uu____1864 -> u2 in
      let uu____1865 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1865
let base_and_refinement_maybe_delta:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                FStar_Syntax_Syntax.term'
                                                                  FStar_Syntax_Syntax.syntax)
                                                                FStar_Pervasives_Native.tuple2
                                                                FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
            else
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF] in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11 in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____1977 = norm_refinement env t12 in
                 match uu____1977 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____1994;
                     FStar_Syntax_Syntax.vars = uu____1995;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2021 =
                       let uu____2022 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2023 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2022 uu____2023 in
                     failwith uu____2021)
          | FStar_Syntax_Syntax.Tm_uinst uu____2038 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2075 =
                   let uu____2076 = FStar_Syntax_Subst.compress t1' in
                   uu____2076.FStar_Syntax_Syntax.n in
                 match uu____2075 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2093 -> aux true t1'
                 | uu____2100 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2115 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2146 =
                   let uu____2147 = FStar_Syntax_Subst.compress t1' in
                   uu____2147.FStar_Syntax_Syntax.n in
                 match uu____2146 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2164 -> aux true t1'
                 | uu____2171 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2186 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2231 =
                   let uu____2232 = FStar_Syntax_Subst.compress t1' in
                   uu____2232.FStar_Syntax_Syntax.n in
                 match uu____2231 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2249 -> aux true t1'
                 | uu____2256 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2271 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2286 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2301 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2316 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2331 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2358 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2389 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2420 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2447 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2484 ->
              let uu____2491 =
                let uu____2492 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2493 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2492 uu____2493 in
              failwith uu____2491
          | FStar_Syntax_Syntax.Tm_ascribed uu____2508 ->
              let uu____2535 =
                let uu____2536 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2537 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2536 uu____2537 in
              failwith uu____2535
          | FStar_Syntax_Syntax.Tm_delayed uu____2552 ->
              let uu____2577 =
                let uu____2578 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2579 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2578 uu____2579 in
              failwith uu____2577
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2594 =
                let uu____2595 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2596 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2595 uu____2596 in
              failwith uu____2594 in
        let uu____2611 = whnf env t1 in aux false uu____2611
let base_and_refinement:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t
let normalize_refinement:
  'Auu____2633 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2633 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2656 = base_and_refinement env t in
      FStar_All.pipe_right uu____2656 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2690 = FStar_Syntax_Syntax.null_bv t in
    (uu____2690, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2696 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2696 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2717 = base_and_refinement_maybe_delta delta1 env t in
          match uu____2717 with
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
  fun uu____2796  ->
    match uu____2796 with
    | (t_base,refopt) ->
        let uu____2823 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2823 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2855 =
      let uu____2858 =
        let uu____2861 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2884  ->
                  match uu____2884 with | (uu____2891,uu____2892,x) -> x)) in
        FStar_List.append wl.attempting uu____2861 in
      FStar_List.map (wl_prob_to_string wl) uu____2858 in
    FStar_All.pipe_right uu____2855 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2905 =
          let uu____2918 =
            let uu____2919 = FStar_Syntax_Subst.compress k in
            uu____2919.FStar_Syntax_Syntax.n in
          match uu____2918 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2972 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2972)
              else
                (let uu____2986 = FStar_Syntax_Util.abs_formals t in
                 match uu____2986 with
                 | (ys',t1,uu____3009) ->
                     let uu____3014 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3014))
          | uu____3055 ->
              let uu____3056 =
                let uu____3067 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3067) in
              ((ys, t), uu____3056) in
        match uu____2905 with
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
                 let uu____3116 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3116 c in
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
            let uu____3144 = p_guard prob in
            match uu____3144 with
            | (uu____3149,uv) ->
                ((let uu____3152 =
                    let uu____3153 = FStar_Syntax_Subst.compress uv in
                    uu____3153.FStar_Syntax_Syntax.n in
                  match uu____3152 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3185 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3185
                        then
                          let uu____3186 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3187 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3188 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3186
                            uu____3187 uu____3188
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3190 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___257_3193 = wl in
                  {
                    attempting = (uu___257_3193.attempting);
                    wl_deferred = (uu___257_3193.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___257_3193.defer_ok);
                    smt_ok = (uu___257_3193.smt_ok);
                    tcenv = (uu___257_3193.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3208 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3208
         then
           let uu____3209 = FStar_Util.string_of_int pid in
           let uu____3210 =
             let uu____3211 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3211 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3209 uu____3210
         else ());
        commit sol;
        (let uu___258_3218 = wl in
         {
           attempting = (uu___258_3218.attempting);
           wl_deferred = (uu___258_3218.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___258_3218.defer_ok);
           smt_ok = (uu___258_3218.smt_ok);
           tcenv = (uu___258_3218.tcenv)
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
            | (uu____3256,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3268 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3268 in
          (let uu____3274 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3274
           then
             let uu____3275 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3276 =
               let uu____3277 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3277 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3275 uu____3276
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
        let uu____3309 =
          let uu____3316 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3316 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3309
          (FStar_Util.for_some
             (fun uu____3352  ->
                match uu____3352 with
                | (uv,uu____3358) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3365 'Auu____3366 .
    'Auu____3366 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3365)
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
            let uu____3398 = occurs wl uk t in Prims.op_Negation uu____3398 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3405 =
                 let uu____3406 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3407 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3406 uu____3407 in
               FStar_Pervasives_Native.Some uu____3405) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3417 'Auu____3418 .
    'Auu____3418 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3417)
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
            let uu____3472 = occurs_check env wl uk t in
            match uu____3472 with
            | (occurs_ok,msg) ->
                let uu____3503 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3503, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3526 'Auu____3527 .
    (FStar_Syntax_Syntax.bv,'Auu____3527) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3526) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3526) FStar_Pervasives_Native.tuple2
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
      let uu____3611 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3665  ->
                fun uu____3666  ->
                  match (uu____3665, uu____3666) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3747 =
                        let uu____3748 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3748 in
                      if uu____3747
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3773 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3773
                         then
                           let uu____3786 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3786)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3611 with | (isect,uu____3827) -> FStar_List.rev isect
let binders_eq:
  'Auu____3852 'Auu____3853 .
    (FStar_Syntax_Syntax.bv,'Auu____3853) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3852) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3908  ->
              fun uu____3909  ->
                match (uu____3908, uu____3909) with
                | ((a,uu____3927),(b,uu____3929)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3943 'Auu____3944 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3944) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3943)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3943)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____3995 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4009  ->
                      match uu____4009 with
                      | (b,uu____4015) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____3995
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4031 -> FStar_Pervasives_Native.None
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
            let uu____4104 = pat_var_opt env seen hd1 in
            (match uu____4104 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4118 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4118
                   then
                     let uu____4119 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4119
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4137 =
      let uu____4138 = FStar_Syntax_Subst.compress t in
      uu____4138.FStar_Syntax_Syntax.n in
    match uu____4137 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4141 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4158;
           FStar_Syntax_Syntax.pos = uu____4159;
           FStar_Syntax_Syntax.vars = uu____4160;_},uu____4161)
        -> true
    | uu____4198 -> false
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
           FStar_Syntax_Syntax.pos = uu____4322;
           FStar_Syntax_Syntax.vars = uu____4323;_},args)
        -> (t, uv, k, args)
    | uu____4391 -> failwith "Not a flex-uvar"
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
      let uu____4468 = destruct_flex_t t in
      match uu____4468 with
      | (t1,uv,k,args) ->
          let uu____4583 = pat_vars env [] args in
          (match uu____4583 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4681 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4762 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4797 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4801 -> false
let head_match: match_result -> match_result =
  fun uu___233_4804  ->
    match uu___233_4804 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4819 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4828 ->
          let uu____4829 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4829 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4840 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4859 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4868 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4895 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4896 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4897 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4914 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4927 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4951) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4957,uu____4958) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5000) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5021;
             FStar_Syntax_Syntax.index = uu____5022;
             FStar_Syntax_Syntax.sort = t2;_},uu____5024)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5031 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5032 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5033 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5046 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5064 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5064
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
            let uu____5085 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5085
            then FullMatch
            else
              (let uu____5087 =
                 let uu____5096 =
                   let uu____5099 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5099 in
                 let uu____5100 =
                   let uu____5103 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5103 in
                 (uu____5096, uu____5100) in
               MisMatch uu____5087)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5109),FStar_Syntax_Syntax.Tm_uinst (g,uu____5111)) ->
            let uu____5120 = head_matches env f g in
            FStar_All.pipe_right uu____5120 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5123 = FStar_Const.eq_const c d in
            if uu____5123
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5130),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5132)) ->
            let uu____5181 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5181
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5188),FStar_Syntax_Syntax.Tm_refine (y,uu____5190)) ->
            let uu____5199 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5199 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5201),uu____5202) ->
            let uu____5207 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5207 head_match
        | (uu____5208,FStar_Syntax_Syntax.Tm_refine (x,uu____5210)) ->
            let uu____5215 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5215 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5216,FStar_Syntax_Syntax.Tm_type
           uu____5217) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5218,FStar_Syntax_Syntax.Tm_arrow uu____5219) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5245),FStar_Syntax_Syntax.Tm_app (head',uu____5247))
            ->
            let uu____5288 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5288 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5290),uu____5291) ->
            let uu____5312 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5312 head_match
        | (uu____5313,FStar_Syntax_Syntax.Tm_app (head1,uu____5315)) ->
            let uu____5336 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5336 head_match
        | uu____5337 ->
            let uu____5342 =
              let uu____5351 = delta_depth_of_term env t11 in
              let uu____5354 = delta_depth_of_term env t21 in
              (uu____5351, uu____5354) in
            MisMatch uu____5342
let head_matches_delta:
  'Auu____5366 .
    FStar_TypeChecker_Env.env ->
      'Auu____5366 ->
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
            let uu____5399 = FStar_Syntax_Util.head_and_args t in
            match uu____5399 with
            | (head1,uu____5417) ->
                let uu____5438 =
                  let uu____5439 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5439.FStar_Syntax_Syntax.n in
                (match uu____5438 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5445 =
                       let uu____5446 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5446 FStar_Option.isSome in
                     if uu____5445
                     then
                       let uu____5465 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5465
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5469 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5572)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5590 =
                     let uu____5599 = maybe_inline t11 in
                     let uu____5602 = maybe_inline t21 in
                     (uu____5599, uu____5602) in
                   match uu____5590 with
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
                (uu____5639,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5657 =
                     let uu____5666 = maybe_inline t11 in
                     let uu____5669 = maybe_inline t21 in
                     (uu____5666, uu____5669) in
                   match uu____5657 with
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
                let uu____5712 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5712 with
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
                let uu____5735 =
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
                (match uu____5735 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5759 -> fail r
            | uu____5768 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5801 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____5837 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___234_5849  ->
    match uu___234_5849 with
    | T (t,uu____5851) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5867 = FStar_Syntax_Util.type_u () in
      match uu____5867 with
      | (t,uu____5873) ->
          let uu____5874 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____5874
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5885 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____5885 FStar_Pervasives_Native.fst
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
        let uu____5949 = head_matches env t1 t' in
        match uu____5949 with
        | MisMatch uu____5950 -> false
        | uu____5959 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6055,imp),T (t2,uu____6058)) -> (t2, imp)
                     | uu____6077 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6144  ->
                    match uu____6144 with
                    | (t2,uu____6158) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6201 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6201 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6276))::tcs2) ->
                       aux
                         (((let uu___259_6311 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___259_6311.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___259_6311.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6329 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___235_6382 =
                 match uu___235_6382 with
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
               let uu____6499 = decompose1 [] bs1 in
               (rebuild, matches, uu____6499))
      | uu____6548 ->
          let rebuild uu___236_6554 =
            match uu___236_6554 with
            | [] -> t1
            | uu____6557 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___237_6588  ->
    match uu___237_6588 with
    | T (t,uu____6590) -> t
    | uu____6599 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___238_6602  ->
    match uu___238_6602 with
    | T (t,uu____6604) -> FStar_Syntax_Syntax.as_arg t
    | uu____6613 -> failwith "Impossible"
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
              | (uu____6719,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6744 = new_uvar r scope1 k in
                  (match uu____6744 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6762 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6779 =
                         let uu____6780 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6780 in
                       ((T (gi_xs, mk_kind)), uu____6779))
              | (uu____6793,uu____6794,C uu____6795) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____6942 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6959;
                         FStar_Syntax_Syntax.vars = uu____6960;_})
                        ->
                        let uu____6983 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6983 with
                         | (T (gi_xs,uu____7007),prob) ->
                             let uu____7017 =
                               let uu____7018 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7018 in
                             (uu____7017, [prob])
                         | uu____7021 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7036;
                         FStar_Syntax_Syntax.vars = uu____7037;_})
                        ->
                        let uu____7060 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7060 with
                         | (T (gi_xs,uu____7084),prob) ->
                             let uu____7094 =
                               let uu____7095 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7095 in
                             (uu____7094, [prob])
                         | uu____7098 -> failwith "impossible")
                    | (uu____7109,uu____7110,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7112;
                         FStar_Syntax_Syntax.vars = uu____7113;_})
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
                        let uu____7244 =
                          let uu____7253 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7253 FStar_List.unzip in
                        (match uu____7244 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7307 =
                                 let uu____7308 =
                                   let uu____7311 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7311 un_T in
                                 let uu____7312 =
                                   let uu____7321 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7321
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7308;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7312;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7307 in
                             ((C gi_xs), sub_probs))
                    | uu____7330 ->
                        let uu____7343 = sub_prob scope1 args q in
                        (match uu____7343 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____6942 with
                   | (tc,probs) ->
                       let uu____7374 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7437,uu____7438),T
                            (t,uu____7440)) ->
                             let b1 =
                               ((let uu___260_7477 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___260_7477.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___260_7477.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7478 =
                               let uu____7485 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7485 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7478)
                         | uu____7520 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7374 with
                        | (bopt,scope2,args1) ->
                            let uu____7604 = aux scope2 args1 qs2 in
                            (match uu____7604 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7641 =
                                         let uu____7644 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7644 in
                                       FStar_Syntax_Util.mk_conj_l uu____7641
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7667 =
                                         let uu____7670 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7671 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7670 :: uu____7671 in
                                       FStar_Syntax_Util.mk_conj_l uu____7667 in
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
  'Auu____7739 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7739)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7739)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___261_7760 = p in
      let uu____7765 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7766 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___261_7760.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7765;
        FStar_TypeChecker_Common.relation =
          (uu___261_7760.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7766;
        FStar_TypeChecker_Common.element =
          (uu___261_7760.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___261_7760.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___261_7760.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___261_7760.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___261_7760.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___261_7760.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7778 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7778
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7787 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____7807 = compress_prob wl pr in
        FStar_All.pipe_right uu____7807 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7817 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____7817 with
           | (lh,uu____7837) ->
               let uu____7858 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____7858 with
                | (rh,uu____7878) ->
                    let uu____7899 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7916,FStar_Syntax_Syntax.Tm_uvar uu____7917)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7954,uu____7955)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____7976,FStar_Syntax_Syntax.Tm_uvar uu____7977)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7998,uu____7999)
                          ->
                          let uu____8016 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8016 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8065 ->
                                    let rank =
                                      let uu____8073 = is_top_level_prob prob in
                                      if uu____8073
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8075 =
                                      let uu___262_8080 = tp in
                                      let uu____8085 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___262_8080.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___262_8080.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___262_8080.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8085;
                                        FStar_TypeChecker_Common.element =
                                          (uu___262_8080.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___262_8080.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___262_8080.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___262_8080.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___262_8080.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___262_8080.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8075)))
                      | (uu____8096,FStar_Syntax_Syntax.Tm_uvar uu____8097)
                          ->
                          let uu____8114 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8114 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8163 ->
                                    let uu____8170 =
                                      let uu___263_8177 = tp in
                                      let uu____8182 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___263_8177.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8182;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___263_8177.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___263_8177.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___263_8177.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___263_8177.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___263_8177.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___263_8177.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___263_8177.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___263_8177.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8170)))
                      | (uu____8199,uu____8200) -> (rigid_rigid, tp) in
                    (match uu____7899 with
                     | (rank,tp1) ->
                         let uu____8219 =
                           FStar_All.pipe_right
                             (let uu___264_8225 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___264_8225.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___264_8225.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___264_8225.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___264_8225.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___264_8225.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___264_8225.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___264_8225.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___264_8225.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___264_8225.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8219))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8235 =
            FStar_All.pipe_right
              (let uu___265_8241 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___265_8241.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___265_8241.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___265_8241.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___265_8241.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___265_8241.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___265_8241.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___265_8241.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___265_8241.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___265_8241.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8235)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8296 probs =
      match uu____8296 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8349 = rank wl hd1 in
               (match uu____8349 with
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
    match projectee with | UDeferred _0 -> true | uu____8456 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8468 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8480 -> false
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
                        let uu____8520 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8520 with
                        | (k,uu____8526) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8536 -> false)))
            | uu____8537 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8588 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8588 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8591 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8601 =
                     let uu____8602 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8603 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8602
                       uu____8603 in
                   UFailed uu____8601)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8623 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8623 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8645 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8645 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8648 ->
                let uu____8653 =
                  let uu____8654 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8655 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8654
                    uu____8655 msg in
                UFailed uu____8653 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8656,uu____8657) ->
              let uu____8658 =
                let uu____8659 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8660 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8659 uu____8660 in
              failwith uu____8658
          | (FStar_Syntax_Syntax.U_unknown ,uu____8661) ->
              let uu____8662 =
                let uu____8663 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8664 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8663 uu____8664 in
              failwith uu____8662
          | (uu____8665,FStar_Syntax_Syntax.U_bvar uu____8666) ->
              let uu____8667 =
                let uu____8668 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8669 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8668 uu____8669 in
              failwith uu____8667
          | (uu____8670,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8671 =
                let uu____8672 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8673 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8672 uu____8673 in
              failwith uu____8671
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8697 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8697
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8719 = occurs_univ v1 u3 in
              if uu____8719
              then
                let uu____8720 =
                  let uu____8721 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8722 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8721 uu____8722 in
                try_umax_components u11 u21 uu____8720
              else
                (let uu____8724 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8724)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8744 = occurs_univ v1 u3 in
              if uu____8744
              then
                let uu____8745 =
                  let uu____8746 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8747 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8746 uu____8747 in
                try_umax_components u11 u21 uu____8745
              else
                (let uu____8749 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8749)
          | (FStar_Syntax_Syntax.U_max uu____8758,uu____8759) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8765 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8765
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8767,FStar_Syntax_Syntax.U_max uu____8768) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8774 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8774
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8776,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8777,FStar_Syntax_Syntax.U_name
             uu____8778) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8779) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8780) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8781,FStar_Syntax_Syntax.U_succ
             uu____8782) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8783,FStar_Syntax_Syntax.U_zero
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
      let uu____8869 = bc1 in
      match uu____8869 with
      | (bs1,mk_cod1) ->
          let uu____8910 = bc2 in
          (match uu____8910 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____8980 = FStar_Util.first_N n1 bs in
                 match uu____8980 with
                 | (bs3,rest) ->
                     let uu____9005 = mk_cod rest in (bs3, uu____9005) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9034 =
                   let uu____9041 = mk_cod1 [] in (bs1, uu____9041) in
                 let uu____9044 =
                   let uu____9051 = mk_cod2 [] in (bs2, uu____9051) in
                 (uu____9034, uu____9044)
               else
                 if l1 > l2
                 then
                   (let uu____9093 = curry l2 bs1 mk_cod1 in
                    let uu____9106 =
                      let uu____9113 = mk_cod2 [] in (bs2, uu____9113) in
                    (uu____9093, uu____9106))
                 else
                   (let uu____9129 =
                      let uu____9136 = mk_cod1 [] in (bs1, uu____9136) in
                    let uu____9139 = curry l1 bs2 mk_cod2 in
                    (uu____9129, uu____9139)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9260 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9260
       then
         let uu____9261 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9261
       else ());
      (let uu____9263 = next_prob probs in
       match uu____9263 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___266_9284 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___266_9284.wl_deferred);
               ctr = (uu___266_9284.ctr);
               defer_ok = (uu___266_9284.defer_ok);
               smt_ok = (uu___266_9284.smt_ok);
               tcenv = (uu___266_9284.tcenv)
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
                  let uu____9295 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9295 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9300 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9300 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9305,uu____9306) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9323 ->
                let uu____9332 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9391  ->
                          match uu____9391 with
                          | (c,uu____9399,uu____9400) -> c < probs.ctr)) in
                (match uu____9332 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9441 =
                            FStar_List.map
                              (fun uu____9456  ->
                                 match uu____9456 with
                                 | (uu____9467,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9441
                      | uu____9470 ->
                          let uu____9479 =
                            let uu___267_9480 = probs in
                            let uu____9481 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9502  ->
                                      match uu____9502 with
                                      | (uu____9509,uu____9510,y) -> y)) in
                            {
                              attempting = uu____9481;
                              wl_deferred = rest;
                              ctr = (uu___267_9480.ctr);
                              defer_ok = (uu___267_9480.defer_ok);
                              smt_ok = (uu___267_9480.smt_ok);
                              tcenv = (uu___267_9480.tcenv)
                            } in
                          solve env uu____9479))))
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
            let uu____9517 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9517 with
            | USolved wl1 ->
                let uu____9519 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9519
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
                  let uu____9565 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9565 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9568 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9580;
                  FStar_Syntax_Syntax.vars = uu____9581;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9584;
                  FStar_Syntax_Syntax.vars = uu____9585;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9599,uu____9600) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9607,FStar_Syntax_Syntax.Tm_uinst uu____9608) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9615 -> USolved wl
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
            ((let uu____9625 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9625
              then
                let uu____9626 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9626 msg
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
        (let uu____9635 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9635
         then
           let uu____9636 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9636
         else ());
        (let uu____9638 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9638 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9700 = head_matches_delta env () t1 t2 in
               match uu____9700 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9741 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____9790 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9805 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____9806 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____9805, uu____9806)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9811 = FStar_Syntax_Subst.compress t1 in
                              let uu____9812 = FStar_Syntax_Subst.compress t2 in
                              (uu____9811, uu____9812) in
                        (match uu____9790 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____9838 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____9838 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____9869 =
                                    let uu____9878 =
                                      let uu____9881 =
                                        let uu____9884 =
                                          let uu____9885 =
                                            let uu____9892 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____9892) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____9885 in
                                        FStar_Syntax_Syntax.mk uu____9884 in
                                      uu____9881 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____9900 =
                                      let uu____9903 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____9903] in
                                    (uu____9878, uu____9900) in
                                  FStar_Pervasives_Native.Some uu____9869
                              | (uu____9916,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9918)) ->
                                  let uu____9923 =
                                    let uu____9930 =
                                      let uu____9933 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____9933] in
                                    (t11, uu____9930) in
                                  FStar_Pervasives_Native.Some uu____9923
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9943),uu____9944) ->
                                  let uu____9949 =
                                    let uu____9956 =
                                      let uu____9959 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____9959] in
                                    (t21, uu____9956) in
                                  FStar_Pervasives_Native.Some uu____9949
                              | uu____9968 ->
                                  let uu____9973 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____9973 with
                                   | (head1,uu____9997) ->
                                       let uu____10018 =
                                         let uu____10019 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10019.FStar_Syntax_Syntax.n in
                                       (match uu____10018 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10030;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10032;_}
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
                                        | uu____10039 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10052) ->
                  let uu____10077 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___239_10103  ->
                            match uu___239_10103 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10110 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10110 with
                                      | (u',uu____10126) ->
                                          let uu____10147 =
                                            let uu____10148 = whnf env u' in
                                            uu____10148.FStar_Syntax_Syntax.n in
                                          (match uu____10147 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10152) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10177 -> false))
                                 | uu____10178 -> false)
                            | uu____10181 -> false)) in
                  (match uu____10077 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10215 tps =
                         match uu____10215 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10263 =
                                    let uu____10272 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10272 in
                                  (match uu____10263 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10307 -> FStar_Pervasives_Native.None) in
                       let uu____10316 =
                         let uu____10325 =
                           let uu____10332 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10332, []) in
                         make_lower_bound uu____10325 lower_bounds in
                       (match uu____10316 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10344 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10344
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
                            ((let uu____10364 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10364
                              then
                                let wl' =
                                  let uu___268_10366 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___268_10366.wl_deferred);
                                    ctr = (uu___268_10366.ctr);
                                    defer_ok = (uu___268_10366.defer_ok);
                                    smt_ok = (uu___268_10366.smt_ok);
                                    tcenv = (uu___268_10366.tcenv)
                                  } in
                                let uu____10367 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10367
                              else ());
                             (let uu____10369 =
                                solve_t env eq_prob
                                  (let uu___269_10371 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___269_10371.wl_deferred);
                                     ctr = (uu___269_10371.ctr);
                                     defer_ok = (uu___269_10371.defer_ok);
                                     smt_ok = (uu___269_10371.smt_ok);
                                     tcenv = (uu___269_10371.tcenv)
                                   }) in
                              match uu____10369 with
                              | Success uu____10374 ->
                                  let wl1 =
                                    let uu___270_10376 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___270_10376.wl_deferred);
                                      ctr = (uu___270_10376.ctr);
                                      defer_ok = (uu___270_10376.defer_ok);
                                      smt_ok = (uu___270_10376.smt_ok);
                                      tcenv = (uu___270_10376.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10378 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10383 -> FStar_Pervasives_Native.None))))
              | uu____10384 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10393 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10393
         then
           let uu____10394 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10394
         else ());
        (let uu____10396 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10396 with
         | (u,args) ->
             let uu____10435 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10435 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10476 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10476 with
                    | (h1,args1) ->
                        let uu____10517 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10517 with
                         | (h2,uu____10537) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10564 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10564
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10582 =
                                          let uu____10585 =
                                            let uu____10586 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10586 in
                                          [uu____10585] in
                                        FStar_Pervasives_Native.Some
                                          uu____10582))
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
                                       (let uu____10619 =
                                          let uu____10622 =
                                            let uu____10623 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10623 in
                                          [uu____10622] in
                                        FStar_Pervasives_Native.Some
                                          uu____10619))
                                  else FStar_Pervasives_Native.None
                              | uu____10637 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10727 =
                               let uu____10736 =
                                 let uu____10739 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10739 in
                               (uu____10736, m1) in
                             FStar_Pervasives_Native.Some uu____10727)
                    | (uu____10752,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10754)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____10802),uu____10803) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____10850 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10903) ->
                       let uu____10928 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___240_10954  ->
                                 match uu___240_10954 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____10961 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____10961 with
                                           | (u',uu____10977) ->
                                               let uu____10998 =
                                                 let uu____10999 =
                                                   whnf env u' in
                                                 uu____10999.FStar_Syntax_Syntax.n in
                                               (match uu____10998 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11003) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11028 -> false))
                                      | uu____11029 -> false)
                                 | uu____11032 -> false)) in
                       (match uu____10928 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11070 tps =
                              match uu____11070 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11132 =
                                         let uu____11143 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11143 in
                                       (match uu____11132 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11194 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11205 =
                              let uu____11216 =
                                let uu____11225 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11225, []) in
                              make_upper_bound uu____11216 upper_bounds in
                            (match uu____11205 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11239 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11239
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
                                 ((let uu____11265 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11265
                                   then
                                     let wl' =
                                       let uu___271_11267 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___271_11267.wl_deferred);
                                         ctr = (uu___271_11267.ctr);
                                         defer_ok = (uu___271_11267.defer_ok);
                                         smt_ok = (uu___271_11267.smt_ok);
                                         tcenv = (uu___271_11267.tcenv)
                                       } in
                                     let uu____11268 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11268
                                   else ());
                                  (let uu____11270 =
                                     solve_t env eq_prob
                                       (let uu___272_11272 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___272_11272.wl_deferred);
                                          ctr = (uu___272_11272.ctr);
                                          defer_ok =
                                            (uu___272_11272.defer_ok);
                                          smt_ok = (uu___272_11272.smt_ok);
                                          tcenv = (uu___272_11272.tcenv)
                                        }) in
                                   match uu____11270 with
                                   | Success uu____11275 ->
                                       let wl1 =
                                         let uu___273_11277 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___273_11277.wl_deferred);
                                           ctr = (uu___273_11277.ctr);
                                           defer_ok =
                                             (uu___273_11277.defer_ok);
                                           smt_ok = (uu___273_11277.smt_ok);
                                           tcenv = (uu___273_11277.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11279 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11284 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11285 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11360 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11360
                      then
                        let uu____11361 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11361
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___274_11415 = hd1 in
                      let uu____11416 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___274_11415.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___274_11415.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11416
                      } in
                    let hd21 =
                      let uu___275_11420 = hd2 in
                      let uu____11421 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___275_11420.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___275_11420.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11421
                      } in
                    let prob =
                      let uu____11425 =
                        let uu____11430 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11430 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11425 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11441 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11441 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11445 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11445 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11483 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11488 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11483 uu____11488 in
                         ((let uu____11498 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11498
                           then
                             let uu____11499 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11500 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11499 uu____11500
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11523 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11533 = aux scope env [] bs1 bs2 in
              match uu____11533 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11557 = compress_tprob wl problem in
        solve_t' env uu____11557 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11590 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11590 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11621,uu____11622) ->
                   let rec may_relate head3 =
                     let uu____11647 =
                       let uu____11648 = FStar_Syntax_Subst.compress head3 in
                       uu____11648.FStar_Syntax_Syntax.n in
                     match uu____11647 with
                     | FStar_Syntax_Syntax.Tm_name uu____11651 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11652 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11675;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11676;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11679;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11680;
                           FStar_Syntax_Syntax.fv_qual = uu____11681;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11685,uu____11686) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11728) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11734) ->
                         may_relate t
                     | uu____11739 -> false in
                   let uu____11740 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11740
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
                                let uu____11757 =
                                  let uu____11758 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11758 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11757 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11760 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11760
                   else
                     (let uu____11762 =
                        let uu____11763 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11764 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11763 uu____11764 in
                      giveup env1 uu____11762 orig)
               | (uu____11765,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___276_11779 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___276_11779.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___276_11779.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___276_11779.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___276_11779.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___276_11779.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___276_11779.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___276_11779.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___276_11779.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____11780,FStar_Pervasives_Native.None ) ->
                   ((let uu____11792 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____11792
                     then
                       let uu____11793 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11794 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____11795 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____11796 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____11793
                         uu____11794 uu____11795 uu____11796
                     else ());
                    (let uu____11798 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____11798 with
                     | (head11,args1) ->
                         let uu____11835 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____11835 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____11889 =
                                  let uu____11890 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____11891 = args_to_string args1 in
                                  let uu____11892 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____11893 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____11890 uu____11891 uu____11892
                                    uu____11893 in
                                giveup env1 uu____11889 orig
                              else
                                (let uu____11895 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____11901 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____11901 = FStar_Syntax_Util.Equal) in
                                 if uu____11895
                                 then
                                   let uu____11902 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____11902 with
                                   | USolved wl2 ->
                                       let uu____11904 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____11904
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____11908 =
                                      base_and_refinement env1 t1 in
                                    match uu____11908 with
                                    | (base1,refinement1) ->
                                        let uu____11933 =
                                          base_and_refinement env1 t2 in
                                        (match uu____11933 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____11990 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____11990 with
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
                                                           (fun uu____12012 
                                                              ->
                                                              fun uu____12013
                                                                 ->
                                                                match 
                                                                  (uu____12012,
                                                                    uu____12013)
                                                                with
                                                                | ((a,uu____12031),
                                                                   (a',uu____12033))
                                                                    ->
                                                                    let uu____12042
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
                                                                    uu____12042)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12052 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12052 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12058 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___277_12094 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___277_12094.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12133 =
          match uu____12133 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12349  ->
                              match uu____12349 with
                              | (x,imp) ->
                                  let uu____12360 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12360, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12373 = FStar_Syntax_Util.type_u () in
                      match uu____12373 with
                      | (t1,uu____12379) ->
                          let uu____12380 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12380 in
                    let uu____12385 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12385 with
                     | (t',tm_u1) ->
                         let uu____12398 = destruct_flex_t t' in
                         (match uu____12398 with
                          | (uu____12435,u1,k1,uu____12438) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12497 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12497 in
                              let sol =
                                let uu____12501 =
                                  let uu____12510 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12510) in
                                TERM uu____12501 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____12646 = pat_var_opt env pat_args hd1 in
                    (match uu____12646 with
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
                                    (fun uu____12709  ->
                                       match uu____12709 with
                                       | (x,uu____12715) ->
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
                            let uu____12730 =
                              let uu____12731 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____12731 in
                            if uu____12730
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____12743 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____12743 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____12758::uu____12759) ->
                    let uu____12790 =
                      let uu____12803 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____12803 in
                    (match uu____12790 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____12842 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____12849::uu____12850,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____12885 =
                let uu____12898 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____12898 in
              (match uu____12885 with
               | (all_formals,res_t) ->
                   let uu____12923 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____12923 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____12957 = lhs in
          match uu____12957 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____12967 ->
                    let uu____12968 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____12968 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____12991 = p in
          match uu____12991 with
          | (((u,k),xs,c),ps,(h,uu____13002,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13084 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13084 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13107 = h gs_xs in
                     let uu____13108 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13107 uu____13108 in
                   ((let uu____13114 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13114
                     then
                       let uu____13115 =
                         let uu____13118 =
                           let uu____13119 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13119
                             (FStar_String.concat "\n\t") in
                         let uu____13124 =
                           let uu____13127 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13128 =
                             let uu____13131 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13132 =
                               let uu____13135 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13136 =
                                 let uu____13139 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13140 =
                                   let uu____13143 =
                                     let uu____13144 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13144
                                       (FStar_String.concat ", ") in
                                   let uu____13149 =
                                     let uu____13152 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13152] in
                                   uu____13143 :: uu____13149 in
                                 uu____13139 :: uu____13140 in
                               uu____13135 :: uu____13136 in
                             uu____13131 :: uu____13132 in
                           uu____13127 :: uu____13128 in
                         uu____13118 :: uu____13124 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13115
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___241_13173 =
          match uu___241_13173 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13205 = p in
          match uu____13205 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13296 = FStar_List.nth ps i in
              (match uu____13296 with
               | (pi,uu____13300) ->
                   let uu____13305 = FStar_List.nth xs i in
                   (match uu____13305 with
                    | (xi,uu____13317) ->
                        let rec gs k =
                          let uu____13330 =
                            let uu____13343 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13343 in
                          match uu____13330 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13418)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13431 = new_uvar r xs k_a in
                                    (match uu____13431 with
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
                                         let uu____13453 = aux subst2 tl1 in
                                         (match uu____13453 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13480 =
                                                let uu____13483 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13483 :: gi_xs' in
                                              let uu____13484 =
                                                let uu____13487 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13487 :: gi_ps' in
                                              (uu____13480, uu____13484))) in
                              aux [] bs in
                        let uu____13492 =
                          let uu____13493 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13493 in
                        if uu____13492
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13497 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13497 with
                           | (g_xs,uu____13509) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13520 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13521 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13520
                                   uu____13521 in
                               let sub1 =
                                 let uu____13527 =
                                   let uu____13532 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13535 =
                                     let uu____13538 =
                                       FStar_List.map
                                         (fun uu____13553  ->
                                            match uu____13553 with
                                            | (uu____13562,uu____13563,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13538 in
                                   mk_problem (p_scope orig) orig uu____13532
                                     (p_rel orig) uu____13535
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13527 in
                               ((let uu____13578 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13578
                                 then
                                   let uu____13579 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13580 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13579 uu____13580
                                 else ());
                                (let wl2 =
                                   let uu____13583 =
                                     let uu____13586 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13586 in
                                   solve_prob orig uu____13583
                                     [TERM (u, proj)] wl1 in
                                 let uu____13595 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13595))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13626 = lhs in
          match uu____13626 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13662 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13662 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13695 =
                        let uu____13742 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13742) in
                      FStar_Pervasives_Native.Some uu____13695
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____13886 =
                           let uu____13893 =
                             let uu____13894 = FStar_Syntax_Subst.compress k1 in
                             uu____13894.FStar_Syntax_Syntax.n in
                           (uu____13893, args) in
                         match uu____13886 with
                         | (uu____13905,[]) ->
                             let uu____13908 =
                               let uu____13919 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____13919) in
                             FStar_Pervasives_Native.Some uu____13908
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13940,uu____13941) ->
                             let uu____13962 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____13962 with
                              | (uv1,uv_args) ->
                                  let uu____14005 =
                                    let uu____14006 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14006.FStar_Syntax_Syntax.n in
                                  (match uu____14005 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14016) ->
                                       let uu____14041 =
                                         pat_vars env [] uv_args in
                                       (match uu____14041 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14068  ->
                                                      let uu____14069 =
                                                        let uu____14070 =
                                                          let uu____14071 =
                                                            let uu____14076 =
                                                              let uu____14077
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14077
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14076 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14071 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14070 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14069)) in
                                            let c1 =
                                              let uu____14087 =
                                                let uu____14088 =
                                                  let uu____14093 =
                                                    let uu____14094 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14094
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14093 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14088 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14087 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14107 =
                                                let uu____14110 =
                                                  let uu____14111 =
                                                    let uu____14114 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14114
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14111 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14110 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14107 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14132 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14137,uu____14138) ->
                             let uu____14157 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14157 with
                              | (uv1,uv_args) ->
                                  let uu____14200 =
                                    let uu____14201 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14201.FStar_Syntax_Syntax.n in
                                  (match uu____14200 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14211) ->
                                       let uu____14236 =
                                         pat_vars env [] uv_args in
                                       (match uu____14236 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14263  ->
                                                      let uu____14264 =
                                                        let uu____14265 =
                                                          let uu____14266 =
                                                            let uu____14271 =
                                                              let uu____14272
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14272
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14271 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14266 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14265 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14264)) in
                                            let c1 =
                                              let uu____14282 =
                                                let uu____14283 =
                                                  let uu____14288 =
                                                    let uu____14289 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14289
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14288 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14283 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14282 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14302 =
                                                let uu____14305 =
                                                  let uu____14306 =
                                                    let uu____14309 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14309
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14306 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14305 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14302 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14327 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14334) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14375 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14375
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14411 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14411 with
                                  | (args1,rest) ->
                                      let uu____14440 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14440 with
                                       | (xs2,c2) ->
                                           let uu____14453 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14453
                                             (fun uu____14477  ->
                                                match uu____14477 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14517 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14517 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14585 =
                                        let uu____14590 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14590 in
                                      FStar_All.pipe_right uu____14585
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14605 ->
                             let uu____14612 =
                               let uu____14613 =
                                 let uu____14618 =
                                   let uu____14619 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14620 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14621 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14619 uu____14620 uu____14621 in
                                 (uu____14618, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14613 in
                             FStar_Exn.raise uu____14612 in
                       let uu____14628 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14628
                         (fun uu____14683  ->
                            match uu____14683 with
                            | (xs1,c1) ->
                                let uu____14732 =
                                  let uu____14773 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____14773) in
                                FStar_Pervasives_Native.Some uu____14732)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____14894 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____14910 = project orig env wl1 i st in
                     match uu____14910 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____14924) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____14939 = imitate orig env wl1 st in
                  match uu____14939 with
                  | Failed uu____14944 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____14975 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____14975 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15000 =
                      let uu____15001 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15001 wl2 in
                    (match uu____15000 with
                     | Failed uu____15002 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15020 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15020 with
                | (hd1,uu____15036) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15057 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15070 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15071 -> true
                     | uu____15088 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15092 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15092
                         then true
                         else
                           ((let uu____15095 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15095
                             then
                               let uu____15096 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15096
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15116 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15116 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15129 =
                            let uu____15130 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15130 in
                          giveup_or_defer1 orig uu____15129
                        else
                          (let uu____15132 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15132
                           then
                             let uu____15133 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15133
                              then
                                let uu____15134 = subterms args_lhs in
                                imitate' orig env wl1 uu____15134
                              else
                                ((let uu____15139 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15139
                                  then
                                    let uu____15140 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15141 = names_to_string fvs1 in
                                    let uu____15142 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15140 uu____15141 uu____15142
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
                               (let uu____15146 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15146
                                then
                                  ((let uu____15148 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15148
                                    then
                                      let uu____15149 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15150 = names_to_string fvs1 in
                                      let uu____15151 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15149 uu____15150 uu____15151
                                    else ());
                                   (let uu____15153 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15153))
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
                     (let uu____15164 =
                        let uu____15165 = FStar_Syntax_Free.names t1 in
                        check_head uu____15165 t2 in
                      if uu____15164
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15176 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15176
                          then
                            let uu____15177 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15178 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15177 uu____15178
                          else ());
                         (let uu____15186 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15186))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15263 uu____15264 r =
               match (uu____15263, uu____15264) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15462 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15462
                   then
                     let uu____15463 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15463
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15487 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15487
                       then
                         let uu____15488 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15489 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15490 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15491 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15492 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15488 uu____15489 uu____15490 uu____15491
                           uu____15492
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15552 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15552 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15566 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15566 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15620 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15620 in
                                  let uu____15623 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15623 k3)
                           else
                             (let uu____15627 =
                                let uu____15628 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15629 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15630 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15628 uu____15629 uu____15630 in
                              failwith uu____15627) in
                       let uu____15631 =
                         let uu____15638 =
                           let uu____15651 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15651 in
                         match uu____15638 with
                         | (bs,k1') ->
                             let uu____15676 =
                               let uu____15689 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15689 in
                             (match uu____15676 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15717 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15717 in
                                  let uu____15726 =
                                    let uu____15731 =
                                      let uu____15732 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15732.FStar_Syntax_Syntax.n in
                                    let uu____15735 =
                                      let uu____15736 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15736.FStar_Syntax_Syntax.n in
                                    (uu____15731, uu____15735) in
                                  (match uu____15726 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15745,uu____15746) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____15749,FStar_Syntax_Syntax.Tm_type
                                      uu____15750) -> (k2'_ys, [sub_prob])
                                   | uu____15753 ->
                                       let uu____15758 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15758 with
                                        | (t,uu____15770) ->
                                            let uu____15771 = new_uvar r zs t in
                                            (match uu____15771 with
                                             | (k_zs,uu____15783) ->
                                                 let kprob =
                                                   let uu____15785 =
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
                                                          _0_64) uu____15785 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15631 with
                       | (k_u',sub_probs) ->
                           let uu____15802 =
                             let uu____15813 =
                               let uu____15814 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15814 in
                             let uu____15823 =
                               let uu____15826 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15826 in
                             let uu____15829 =
                               let uu____15832 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15832 in
                             (uu____15813, uu____15823, uu____15829) in
                           (match uu____15802 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15851 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15851 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15870 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15870
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15874 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15874 with
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
             let solve_one_pat uu____15927 uu____15928 =
               match (uu____15927, uu____15928) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16046 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16046
                     then
                       let uu____16047 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16048 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16047 uu____16048
                     else ());
                    (let uu____16050 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16050
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16069  ->
                              fun uu____16070  ->
                                match (uu____16069, uu____16070) with
                                | ((a,uu____16088),(t21,uu____16090)) ->
                                    let uu____16099 =
                                      let uu____16104 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16104
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16099
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16110 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16110 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16125 = occurs_check env wl (u1, k1) t21 in
                        match uu____16125 with
                        | (occurs_ok,uu____16133) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16141 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16141
                            then
                              let sol =
                                let uu____16143 =
                                  let uu____16152 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16152) in
                                TERM uu____16143 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16159 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16159
                               then
                                 let uu____16160 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16160 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16184,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16210 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16210
                                       then
                                         let uu____16211 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16211
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16218 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16220 = lhs in
             match uu____16220 with
             | (t1,u1,k1,args1) ->
                 let uu____16225 = rhs in
                 (match uu____16225 with
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
                       | uu____16265 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16275 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16275 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16293) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16300 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16300
                                    then
                                      let uu____16301 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16301
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16308 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16310 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16310
        then
          let uu____16311 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16311
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16315 = FStar_Util.physical_equality t1 t2 in
           if uu____16315
           then
             let uu____16316 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16316
           else
             ((let uu____16319 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16319
               then
                 let uu____16320 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16320
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16323,uu____16324) ->
                   let uu____16351 =
                     let uu___278_16352 = problem in
                     let uu____16353 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___278_16352.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16353;
                       FStar_TypeChecker_Common.relation =
                         (uu___278_16352.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___278_16352.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___278_16352.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___278_16352.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___278_16352.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___278_16352.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___278_16352.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___278_16352.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16351 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16354,uu____16355) ->
                   let uu____16362 =
                     let uu___278_16363 = problem in
                     let uu____16364 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___278_16363.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16364;
                       FStar_TypeChecker_Common.relation =
                         (uu___278_16363.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___278_16363.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___278_16363.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___278_16363.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___278_16363.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___278_16363.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___278_16363.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___278_16363.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16362 wl
               | (uu____16365,FStar_Syntax_Syntax.Tm_ascribed uu____16366) ->
                   let uu____16393 =
                     let uu___279_16394 = problem in
                     let uu____16395 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___279_16394.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___279_16394.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___279_16394.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16395;
                       FStar_TypeChecker_Common.element =
                         (uu___279_16394.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___279_16394.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___279_16394.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___279_16394.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___279_16394.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___279_16394.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16393 wl
               | (uu____16396,FStar_Syntax_Syntax.Tm_meta uu____16397) ->
                   let uu____16404 =
                     let uu___279_16405 = problem in
                     let uu____16406 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___279_16405.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___279_16405.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___279_16405.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16406;
                       FStar_TypeChecker_Common.element =
                         (uu___279_16405.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___279_16405.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___279_16405.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___279_16405.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___279_16405.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___279_16405.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16404 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16407,uu____16408) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16409,FStar_Syntax_Syntax.Tm_bvar uu____16410) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___242_16465 =
                     match uu___242_16465 with
                     | [] -> c
                     | bs ->
                         let uu____16487 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16487 in
                   let uu____16496 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16496 with
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
                                   let uu____16638 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16638
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16640 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16640))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___243_16716 =
                     match uu___243_16716 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16750 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16750 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16886 =
                                   let uu____16891 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16892 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16891
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16892 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16886))
               | (FStar_Syntax_Syntax.Tm_abs uu____16897,uu____16898) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____16923 -> true
                     | uu____16940 -> false in
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
                       (let uu____16987 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___280_16995 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___280_16995.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___280_16995.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___280_16995.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___280_16995.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___280_16995.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___280_16995.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___280_16995.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___280_16995.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___280_16995.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___280_16995.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___280_16995.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___280_16995.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___280_16995.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___280_16995.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___280_16995.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___280_16995.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___280_16995.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___280_16995.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___280_16995.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___280_16995.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___280_16995.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___280_16995.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___280_16995.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___280_16995.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___280_16995.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___280_16995.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___280_16995.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___280_16995.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___280_16995.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___280_16995.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___280_16995.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____16987 with
                        | (uu____16998,ty,uu____17000) ->
                            let uu____17001 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17001) in
                   let uu____17002 =
                     let uu____17019 = maybe_eta t1 in
                     let uu____17026 = maybe_eta t2 in
                     (uu____17019, uu____17026) in
                   (match uu____17002 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___281_17068 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___281_17068.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___281_17068.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___281_17068.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___281_17068.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___281_17068.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___281_17068.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___281_17068.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___281_17068.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17091 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17091
                        then
                          let uu____17092 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17092 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17107 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17107.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17107.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17107.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17107.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17107.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17107.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17107.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17107.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17131 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17131
                        then
                          let uu____17132 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17132 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17147 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17147.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17147.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17147.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17147.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17147.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17147.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17147.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17147.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17151 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17168,FStar_Syntax_Syntax.Tm_abs uu____17169) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17194 -> true
                     | uu____17211 -> false in
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
                       (let uu____17258 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___280_17266 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___280_17266.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___280_17266.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___280_17266.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___280_17266.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___280_17266.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___280_17266.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___280_17266.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___280_17266.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___280_17266.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___280_17266.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___280_17266.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___280_17266.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___280_17266.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___280_17266.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___280_17266.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___280_17266.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___280_17266.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___280_17266.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___280_17266.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___280_17266.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___280_17266.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___280_17266.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___280_17266.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___280_17266.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___280_17266.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___280_17266.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___280_17266.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___280_17266.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___280_17266.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___280_17266.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___280_17266.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17258 with
                        | (uu____17269,ty,uu____17271) ->
                            let uu____17272 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17272) in
                   let uu____17273 =
                     let uu____17290 = maybe_eta t1 in
                     let uu____17297 = maybe_eta t2 in
                     (uu____17290, uu____17297) in
                   (match uu____17273 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___281_17339 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___281_17339.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___281_17339.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___281_17339.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___281_17339.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___281_17339.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___281_17339.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___281_17339.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___281_17339.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17362 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17362
                        then
                          let uu____17363 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17363 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17378 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17378.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17378.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17378.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17378.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17378.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17378.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17378.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17378.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17402 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17402
                        then
                          let uu____17403 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17403 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17418 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17418.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17418.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17418.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17418.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17418.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17418.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17418.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17418.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17422 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____17454 = FStar_Syntax_Free.uvars t1 in
                       FStar_Util.set_is_empty uu____17454) &&
                        (let uu____17466 = FStar_Syntax_Free.uvars t2 in
                         FStar_Util.set_is_empty uu____17466))
                       &&
                       (let uu____17481 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort in
                        match uu____17481 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___244_17491 =
                              match uu___244_17491 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____17492 -> true
                              | uu____17493 -> false in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____17494 -> false) in
                   let uu____17495 = as_refinement should_delta env wl t1 in
                   (match uu____17495 with
                    | (x11,phi1) ->
                        let uu____17502 =
                          as_refinement should_delta env wl t2 in
                        (match uu____17502 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____17510 =
                                 mk_problem (p_scope orig) orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17510 in
                             let x12 = FStar_Syntax_Syntax.freshen_bv x11 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x12)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi22 =
                               FStar_Syntax_Subst.subst subst1 phi21 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x12 in
                             let mk_imp1 imp phi12 phi23 =
                               let uu____17548 = imp phi12 phi23 in
                               FStar_All.pipe_right uu____17548
                                 (guard_on_element wl problem x12) in
                             let fallback uu____17552 =
                               let impl =
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                     phi22
                                 else
                                   mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                     phi22 in
                               let guard =
                                 let uu____17558 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17558 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17567 =
                                   let uu____17572 =
                                     let uu____17573 =
                                       let uu____17580 =
                                         FStar_Syntax_Syntax.mk_binder x12 in
                                       [uu____17580] in
                                     FStar_List.append (p_scope orig)
                                       uu____17573 in
                                   mk_problem uu____17572 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17567 in
                               let uu____17589 =
                                 solve env1
                                   (let uu___283_17591 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___283_17591.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___283_17591.smt_ok);
                                      tcenv = (uu___283_17591.tcenv)
                                    }) in
                               (match uu____17589 with
                                | Failed uu____17598 -> fallback ()
                                | Success uu____17603 ->
                                    let guard =
                                      let uu____17607 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17612 =
                                        let uu____17613 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17613
                                          (guard_on_element wl problem x12) in
                                      FStar_Syntax_Util.mk_conj uu____17607
                                        uu____17612 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___284_17622 = wl1 in
                                      {
                                        attempting =
                                          (uu___284_17622.attempting);
                                        wl_deferred =
                                          (uu___284_17622.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___284_17622.defer_ok);
                                        smt_ok = (uu___284_17622.smt_ok);
                                        tcenv = (uu___284_17622.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17624,FStar_Syntax_Syntax.Tm_uvar uu____17625) ->
                   let uu____17658 = destruct_flex_t t1 in
                   let uu____17659 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17658 uu____17659
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17660;
                     FStar_Syntax_Syntax.pos = uu____17661;
                     FStar_Syntax_Syntax.vars = uu____17662;_},uu____17663),FStar_Syntax_Syntax.Tm_uvar
                  uu____17664) ->
                   let uu____17717 = destruct_flex_t t1 in
                   let uu____17718 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17717 uu____17718
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17719,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17720;
                     FStar_Syntax_Syntax.pos = uu____17721;
                     FStar_Syntax_Syntax.vars = uu____17722;_},uu____17723))
                   ->
                   let uu____17776 = destruct_flex_t t1 in
                   let uu____17777 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17776 uu____17777
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17778;
                     FStar_Syntax_Syntax.pos = uu____17779;
                     FStar_Syntax_Syntax.vars = uu____17780;_},uu____17781),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17782;
                     FStar_Syntax_Syntax.pos = uu____17783;
                     FStar_Syntax_Syntax.vars = uu____17784;_},uu____17785))
                   ->
                   let uu____17858 = destruct_flex_t t1 in
                   let uu____17859 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17858 uu____17859
               | (FStar_Syntax_Syntax.Tm_uvar uu____17860,uu____17861) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17878 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17878 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17885;
                     FStar_Syntax_Syntax.pos = uu____17886;
                     FStar_Syntax_Syntax.vars = uu____17887;_},uu____17888),uu____17889)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17926 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17926 t2 wl
               | (uu____17933,FStar_Syntax_Syntax.Tm_uvar uu____17934) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____17951,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17952;
                     FStar_Syntax_Syntax.pos = uu____17953;
                     FStar_Syntax_Syntax.vars = uu____17954;_},uu____17955))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17992,FStar_Syntax_Syntax.Tm_type uu____17993) ->
                   solve_t' env
                     (let uu___285_18011 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18011.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18011.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18011.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18011.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18011.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18011.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18011.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18011.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18011.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18012;
                     FStar_Syntax_Syntax.pos = uu____18013;
                     FStar_Syntax_Syntax.vars = uu____18014;_},uu____18015),FStar_Syntax_Syntax.Tm_type
                  uu____18016) ->
                   solve_t' env
                     (let uu___285_18054 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18054.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18054.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18054.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18054.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18054.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18054.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18054.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18054.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18054.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18055,FStar_Syntax_Syntax.Tm_arrow uu____18056) ->
                   solve_t' env
                     (let uu___285_18086 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18086.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18086.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18086.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18086.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18086.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18086.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18086.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18086.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18086.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18087;
                     FStar_Syntax_Syntax.pos = uu____18088;
                     FStar_Syntax_Syntax.vars = uu____18089;_},uu____18090),FStar_Syntax_Syntax.Tm_arrow
                  uu____18091) ->
                   solve_t' env
                     (let uu___285_18141 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18141.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18141.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18141.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18141.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18141.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18141.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18141.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18141.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18141.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18142,uu____18143) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18162 =
                        let uu____18163 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18163 in
                      if uu____18162
                      then
                        let uu____18164 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___286_18170 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___286_18170.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___286_18170.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___286_18170.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___286_18170.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___286_18170.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___286_18170.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___286_18170.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___286_18170.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___286_18170.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18171 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18164 uu____18171 t2
                          wl
                      else
                        (let uu____18179 = base_and_refinement env t2 in
                         match uu____18179 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18208 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___287_18214 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___287_18214.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___287_18214.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___287_18214.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___287_18214.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___287_18214.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___287_18214.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___287_18214.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___287_18214.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___287_18214.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18215 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18208
                                    uu____18215 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___288_18229 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___288_18229.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___288_18229.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18232 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18232 in
                                  let guard =
                                    let uu____18244 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18244
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18252;
                     FStar_Syntax_Syntax.pos = uu____18253;
                     FStar_Syntax_Syntax.vars = uu____18254;_},uu____18255),uu____18256)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18295 =
                        let uu____18296 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18296 in
                      if uu____18295
                      then
                        let uu____18297 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___286_18303 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___286_18303.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___286_18303.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___286_18303.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___286_18303.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___286_18303.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___286_18303.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___286_18303.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___286_18303.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___286_18303.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18304 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18297 uu____18304 t2
                          wl
                      else
                        (let uu____18312 = base_and_refinement env t2 in
                         match uu____18312 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18341 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___287_18347 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___287_18347.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___287_18347.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___287_18347.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___287_18347.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___287_18347.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___287_18347.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___287_18347.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___287_18347.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___287_18347.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18348 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18341
                                    uu____18348 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___288_18362 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___288_18362.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___288_18362.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18365 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18365 in
                                  let guard =
                                    let uu____18377 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18377
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18385,FStar_Syntax_Syntax.Tm_uvar uu____18386) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18404 = base_and_refinement env t1 in
                      match uu____18404 with
                      | (t_base,uu____18416) ->
                          solve_t env
                            (let uu___289_18430 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___289_18430.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___289_18430.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___289_18430.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___289_18430.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___289_18430.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___289_18430.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___289_18430.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___289_18430.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18431,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18432;
                     FStar_Syntax_Syntax.pos = uu____18433;
                     FStar_Syntax_Syntax.vars = uu____18434;_},uu____18435))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18473 = base_and_refinement env t1 in
                      match uu____18473 with
                      | (t_base,uu____18485) ->
                          solve_t env
                            (let uu___289_18499 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___289_18499.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___289_18499.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___289_18499.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___289_18499.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___289_18499.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___289_18499.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___289_18499.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___289_18499.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18500,uu____18501) ->
                   let t21 =
                     let uu____18511 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18511 in
                   solve_t env
                     (let uu___290_18535 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___290_18535.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___290_18535.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___290_18535.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___290_18535.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___290_18535.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___290_18535.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___290_18535.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___290_18535.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___290_18535.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18536,FStar_Syntax_Syntax.Tm_refine uu____18537) ->
                   let t11 =
                     let uu____18547 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18547 in
                   solve_t env
                     (let uu___291_18571 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___291_18571.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___291_18571.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___291_18571.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___291_18571.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___291_18571.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___291_18571.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___291_18571.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___291_18571.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___291_18571.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18574,uu____18575) ->
                   let head1 =
                     let uu____18601 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18601
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18645 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18645
                       FStar_Pervasives_Native.fst in
                   let uu____18686 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18686
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18701 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18701
                      then
                        let guard =
                          let uu____18713 =
                            let uu____18714 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18714 = FStar_Syntax_Util.Equal in
                          if uu____18713
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18718 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18718) in
                        let uu____18721 = solve_prob orig guard [] wl in
                        solve env uu____18721
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18724,uu____18725) ->
                   let head1 =
                     let uu____18735 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18735
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18779 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18779
                       FStar_Pervasives_Native.fst in
                   let uu____18820 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18820
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18835 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18835
                      then
                        let guard =
                          let uu____18847 =
                            let uu____18848 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18848 = FStar_Syntax_Util.Equal in
                          if uu____18847
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18852 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18852) in
                        let uu____18855 = solve_prob orig guard [] wl in
                        solve env uu____18855
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18858,uu____18859) ->
                   let head1 =
                     let uu____18863 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18863
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18907 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18907
                       FStar_Pervasives_Native.fst in
                   let uu____18948 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18948
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18963 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18963
                      then
                        let guard =
                          let uu____18975 =
                            let uu____18976 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18976 = FStar_Syntax_Util.Equal in
                          if uu____18975
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18980 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____18980) in
                        let uu____18983 = solve_prob orig guard [] wl in
                        solve env uu____18983
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____18986,uu____18987) ->
                   let head1 =
                     let uu____18991 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18991
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19035 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19035
                       FStar_Pervasives_Native.fst in
                   let uu____19076 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19076
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19091 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19091
                      then
                        let guard =
                          let uu____19103 =
                            let uu____19104 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19104 = FStar_Syntax_Util.Equal in
                          if uu____19103
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19108 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19108) in
                        let uu____19111 = solve_prob orig guard [] wl in
                        solve env uu____19111
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19114,uu____19115) ->
                   let head1 =
                     let uu____19119 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19119
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19163 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19163
                       FStar_Pervasives_Native.fst in
                   let uu____19204 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19204
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19219 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19219
                      then
                        let guard =
                          let uu____19231 =
                            let uu____19232 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19232 = FStar_Syntax_Util.Equal in
                          if uu____19231
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19236 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19236) in
                        let uu____19239 = solve_prob orig guard [] wl in
                        solve env uu____19239
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19242,uu____19243) ->
                   let head1 =
                     let uu____19261 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19261
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19305 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19305
                       FStar_Pervasives_Native.fst in
                   let uu____19346 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19346
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19361 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19361
                      then
                        let guard =
                          let uu____19373 =
                            let uu____19374 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19374 = FStar_Syntax_Util.Equal in
                          if uu____19373
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19378 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19378) in
                        let uu____19381 = solve_prob orig guard [] wl in
                        solve env uu____19381
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19384,FStar_Syntax_Syntax.Tm_match uu____19385) ->
                   let head1 =
                     let uu____19411 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19411
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19455 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19455
                       FStar_Pervasives_Native.fst in
                   let uu____19496 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19496
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19511 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19511
                      then
                        let guard =
                          let uu____19523 =
                            let uu____19524 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19524 = FStar_Syntax_Util.Equal in
                          if uu____19523
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19528 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19528) in
                        let uu____19531 = solve_prob orig guard [] wl in
                        solve env uu____19531
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19534,FStar_Syntax_Syntax.Tm_uinst uu____19535) ->
                   let head1 =
                     let uu____19545 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19545
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19589 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19589
                       FStar_Pervasives_Native.fst in
                   let uu____19630 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19630
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19645 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19645
                      then
                        let guard =
                          let uu____19657 =
                            let uu____19658 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19658 = FStar_Syntax_Util.Equal in
                          if uu____19657
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19662 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19662) in
                        let uu____19665 = solve_prob orig guard [] wl in
                        solve env uu____19665
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19668,FStar_Syntax_Syntax.Tm_name uu____19669) ->
                   let head1 =
                     let uu____19673 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19673
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19717 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19717
                       FStar_Pervasives_Native.fst in
                   let uu____19758 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19758
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19773 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19773
                      then
                        let guard =
                          let uu____19785 =
                            let uu____19786 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19786 = FStar_Syntax_Util.Equal in
                          if uu____19785
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19790 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19790) in
                        let uu____19793 = solve_prob orig guard [] wl in
                        solve env uu____19793
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19796,FStar_Syntax_Syntax.Tm_constant uu____19797) ->
                   let head1 =
                     let uu____19801 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19801
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19845 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19845
                       FStar_Pervasives_Native.fst in
                   let uu____19886 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19886
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19901 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19901
                      then
                        let guard =
                          let uu____19913 =
                            let uu____19914 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19914 = FStar_Syntax_Util.Equal in
                          if uu____19913
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19918 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19918) in
                        let uu____19921 = solve_prob orig guard [] wl in
                        solve env uu____19921
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19924,FStar_Syntax_Syntax.Tm_fvar uu____19925) ->
                   let head1 =
                     let uu____19929 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19929
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19973 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19973
                       FStar_Pervasives_Native.fst in
                   let uu____20014 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20014
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20029 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20029
                      then
                        let guard =
                          let uu____20041 =
                            let uu____20042 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20042 = FStar_Syntax_Util.Equal in
                          if uu____20041
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20046 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20046) in
                        let uu____20049 = solve_prob orig guard [] wl in
                        solve env uu____20049
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20052,FStar_Syntax_Syntax.Tm_app uu____20053) ->
                   let head1 =
                     let uu____20071 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20071
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20115 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20115
                       FStar_Pervasives_Native.fst in
                   let uu____20156 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20156
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20171 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20171
                      then
                        let guard =
                          let uu____20183 =
                            let uu____20184 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20184 = FStar_Syntax_Util.Equal in
                          if uu____20183
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20188 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20188) in
                        let uu____20191 = solve_prob orig guard [] wl in
                        solve env uu____20191
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20194,uu____20195) ->
                   let uu____20208 =
                     let uu____20209 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20210 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20209
                       uu____20210 in
                   failwith uu____20208
               | (FStar_Syntax_Syntax.Tm_delayed uu____20211,uu____20212) ->
                   let uu____20237 =
                     let uu____20238 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20239 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20238
                       uu____20239 in
                   failwith uu____20237
               | (uu____20240,FStar_Syntax_Syntax.Tm_delayed uu____20241) ->
                   let uu____20266 =
                     let uu____20267 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20268 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20267
                       uu____20268 in
                   failwith uu____20266
               | (uu____20269,FStar_Syntax_Syntax.Tm_let uu____20270) ->
                   let uu____20283 =
                     let uu____20284 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20285 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20284
                       uu____20285 in
                   failwith uu____20283
               | uu____20286 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20322 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20322
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20324 =
               let uu____20325 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20326 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20325 uu____20326 in
             giveup env uu____20324 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20346  ->
                    fun uu____20347  ->
                      match (uu____20346, uu____20347) with
                      | ((a1,uu____20365),(a2,uu____20367)) ->
                          let uu____20376 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20376)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20386 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20386 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20410 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20417)::[] -> wp1
              | uu____20434 ->
                  let uu____20443 =
                    let uu____20444 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20444 in
                  failwith uu____20443 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20452 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____20452]
              | x -> x in
            let uu____20454 =
              let uu____20463 =
                let uu____20464 =
                  let uu____20465 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20465 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20464 in
              [uu____20463] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20454;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20466 = lift_c1 () in solve_eq uu____20466 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___245_20472  ->
                       match uu___245_20472 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20473 -> false)) in
             let uu____20474 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20508)::uu____20509,(wp2,uu____20511)::uu____20512)
                   -> (wp1, wp2)
               | uu____20569 ->
                   let uu____20590 =
                     let uu____20591 =
                       let uu____20596 =
                         let uu____20597 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20598 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20597 uu____20598 in
                       (uu____20596, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20591 in
                   FStar_Exn.raise uu____20590 in
             match uu____20474 with
             | (wpc1,wpc2) ->
                 let uu____20617 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20617
                 then
                   let uu____20620 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20620 wl
                 else
                   (let uu____20624 =
                      let uu____20631 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20631 in
                    match uu____20624 with
                    | (c2_decl,qualifiers) ->
                        let uu____20652 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20652
                        then
                          let c1_repr =
                            let uu____20656 =
                              let uu____20657 =
                                let uu____20658 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20658 in
                              let uu____20659 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20657 uu____20659 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20656 in
                          let c2_repr =
                            let uu____20661 =
                              let uu____20662 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20663 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20662 uu____20663 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20661 in
                          let prob =
                            let uu____20665 =
                              let uu____20670 =
                                let uu____20671 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20672 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20671
                                  uu____20672 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20670 in
                            FStar_TypeChecker_Common.TProb uu____20665 in
                          let wl1 =
                            let uu____20674 =
                              let uu____20677 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20677 in
                            solve_prob orig uu____20674 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20686 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20686
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____20689 =
                                     let uu____20692 =
                                       let uu____20693 =
                                         let uu____20708 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20709 =
                                           let uu____20712 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20713 =
                                             let uu____20716 =
                                               let uu____20717 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20717 in
                                             [uu____20716] in
                                           uu____20712 :: uu____20713 in
                                         (uu____20708, uu____20709) in
                                       FStar_Syntax_Syntax.Tm_app uu____20693 in
                                     FStar_Syntax_Syntax.mk uu____20692 in
                                   uu____20689 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____20726 =
                                    let uu____20729 =
                                      let uu____20730 =
                                        let uu____20745 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20746 =
                                          let uu____20749 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20750 =
                                            let uu____20753 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20754 =
                                              let uu____20757 =
                                                let uu____20758 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20758 in
                                              [uu____20757] in
                                            uu____20753 :: uu____20754 in
                                          uu____20749 :: uu____20750 in
                                        (uu____20745, uu____20746) in
                                      FStar_Syntax_Syntax.Tm_app uu____20730 in
                                    FStar_Syntax_Syntax.mk uu____20729 in
                                  uu____20726 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20765 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20765 in
                           let wl1 =
                             let uu____20775 =
                               let uu____20778 =
                                 let uu____20781 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20781 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20778 in
                             solve_prob orig uu____20775 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20794 = FStar_Util.physical_equality c1 c2 in
        if uu____20794
        then
          let uu____20795 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20795
        else
          ((let uu____20798 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20798
            then
              let uu____20799 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20800 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20799
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20800
            else ());
           (let uu____20802 =
              let uu____20807 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20808 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20807, uu____20808) in
            match uu____20802 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20812),FStar_Syntax_Syntax.Total
                    (t2,uu____20814)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20831 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20831 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20834,FStar_Syntax_Syntax.Total uu____20835) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20853),FStar_Syntax_Syntax.Total
                    (t2,uu____20855)) ->
                     let uu____20872 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20872 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20876),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20878)) ->
                     let uu____20895 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20895 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20899),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20901)) ->
                     let uu____20918 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20918 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20921,FStar_Syntax_Syntax.Comp uu____20922) ->
                     let uu____20931 =
                       let uu___292_20936 = problem in
                       let uu____20941 =
                         let uu____20942 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20942 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___292_20936.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20941;
                         FStar_TypeChecker_Common.relation =
                           (uu___292_20936.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___292_20936.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___292_20936.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___292_20936.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___292_20936.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___292_20936.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___292_20936.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___292_20936.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20931 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20943,FStar_Syntax_Syntax.Comp uu____20944) ->
                     let uu____20953 =
                       let uu___292_20958 = problem in
                       let uu____20963 =
                         let uu____20964 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20964 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___292_20958.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20963;
                         FStar_TypeChecker_Common.relation =
                           (uu___292_20958.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___292_20958.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___292_20958.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___292_20958.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___292_20958.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___292_20958.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___292_20958.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___292_20958.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20953 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20965,FStar_Syntax_Syntax.GTotal uu____20966) ->
                     let uu____20975 =
                       let uu___293_20980 = problem in
                       let uu____20985 =
                         let uu____20986 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20986 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___293_20980.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___293_20980.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___293_20980.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20985;
                         FStar_TypeChecker_Common.element =
                           (uu___293_20980.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___293_20980.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___293_20980.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___293_20980.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___293_20980.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___293_20980.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20975 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20987,FStar_Syntax_Syntax.Total uu____20988) ->
                     let uu____20997 =
                       let uu___293_21002 = problem in
                       let uu____21007 =
                         let uu____21008 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21008 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___293_21002.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___293_21002.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___293_21002.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21007;
                         FStar_TypeChecker_Common.element =
                           (uu___293_21002.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___293_21002.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___293_21002.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___293_21002.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___293_21002.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___293_21002.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20997 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21009,FStar_Syntax_Syntax.Comp uu____21010) ->
                     let uu____21011 =
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
                     if uu____21011
                     then
                       let uu____21012 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21012 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21018 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21028 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21029 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21028, uu____21029)) in
                          match uu____21018 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21036 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21036
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21038 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21038 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21041 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21043 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21043) in
                                if uu____21041
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
                                  (let uu____21046 =
                                     let uu____21047 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21048 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21047 uu____21048 in
                                   giveup env uu____21046 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21053 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21091  ->
              match uu____21091 with
              | (uu____21104,uu____21105,u,uu____21107,uu____21108,uu____21109)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21053 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21140 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21140 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21158 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21186  ->
                match uu____21186 with
                | (u1,u2) ->
                    let uu____21193 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21194 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21193 uu____21194)) in
      FStar_All.pipe_right uu____21158 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21211,[])) -> "{}"
      | uu____21236 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21253 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21253
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21256 =
              FStar_List.map
                (fun uu____21266  ->
                   match uu____21266 with
                   | (uu____21271,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21256 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21276 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21276 imps
let new_t_problem:
  'Auu____21284 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21284 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21284)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21318 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21318
                then
                  let uu____21319 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21320 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21319
                    (rel_to_string rel) uu____21320
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
            let uu____21344 =
              let uu____21347 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21347 in
            FStar_Syntax_Syntax.new_bv uu____21344 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21356 =
              let uu____21359 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21359 in
            let uu____21362 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21356 uu____21362 in
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
          let uu____21392 = FStar_Options.eager_inference () in
          if uu____21392
          then
            let uu___294_21393 = probs in
            {
              attempting = (uu___294_21393.attempting);
              wl_deferred = (uu___294_21393.wl_deferred);
              ctr = (uu___294_21393.ctr);
              defer_ok = false;
              smt_ok = (uu___294_21393.smt_ok);
              tcenv = (uu___294_21393.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21404 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21404
              then
                let uu____21405 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21405
              else ());
             (let result = err1 (d, s) in
              FStar_Syntax_Unionfind.rollback tx; result))
let simplify_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____21419 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21419
            then
              let uu____21420 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21420
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____21424 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21424
             then
               let uu____21425 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21425
             else ());
            (let f2 =
               let uu____21428 =
                 let uu____21429 = FStar_Syntax_Util.unmeta f1 in
                 uu____21429.FStar_Syntax_Syntax.n in
               match uu____21428 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21433 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___295_21434 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___295_21434.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___295_21434.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___295_21434.FStar_TypeChecker_Env.implicits)
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
            let uu____21453 =
              let uu____21454 =
                let uu____21455 =
                  let uu____21456 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21456
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21455;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21454 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21453
let with_guard_no_simp:
  'Auu____21483 .
    'Auu____21483 ->
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
            let uu____21503 =
              let uu____21504 =
                let uu____21505 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21505
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21504;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21503
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
          (let uu____21543 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21543
           then
             let uu____21544 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21545 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21544
               uu____21545
           else ());
          (let prob =
             let uu____21548 =
               let uu____21553 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21553 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21548 in
           let g =
             let uu____21561 =
               let uu____21564 = singleton' env prob smt_ok in
               solve_and_commit env uu____21564
                 (fun uu____21566  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21561 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21584 = try_teq true env t1 t2 in
        match uu____21584 with
        | FStar_Pervasives_Native.None  ->
            let uu____21587 =
              let uu____21588 =
                let uu____21593 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21594 = FStar_TypeChecker_Env.get_range env in
                (uu____21593, uu____21594) in
              FStar_Errors.Error uu____21588 in
            FStar_Exn.raise uu____21587
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21597 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21597
              then
                let uu____21598 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21599 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21600 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21598
                  uu____21599 uu____21600
              else ());
             g)
let subtype_fail:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____21614 = FStar_TypeChecker_Env.get_range env in
          let uu____21615 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21614 uu____21615
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21628 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21628
         then
           let uu____21629 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21630 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21629
             uu____21630
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21635 =
             let uu____21640 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21640 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21635 in
         let uu____21645 =
           let uu____21648 = singleton env prob in
           solve_and_commit env uu____21648
             (fun uu____21650  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21645)
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
      fun uu____21679  ->
        match uu____21679 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21718 =
                 let uu____21719 =
                   let uu____21724 =
                     let uu____21725 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21726 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21725 uu____21726 in
                   let uu____21727 = FStar_TypeChecker_Env.get_range env in
                   (uu____21724, uu____21727) in
                 FStar_Errors.Error uu____21719 in
               FStar_Exn.raise uu____21718) in
            let equiv1 v1 v' =
              let uu____21735 =
                let uu____21740 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21741 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21740, uu____21741) in
              match uu____21735 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21760 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21790 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21790 with
                      | FStar_Syntax_Syntax.U_unif uu____21797 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21826  ->
                                    match uu____21826 with
                                    | (u,v') ->
                                        let uu____21835 = equiv1 v1 v' in
                                        if uu____21835
                                        then
                                          let uu____21838 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21838 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21854 -> [])) in
            let uu____21859 =
              let wl =
                let uu___296_21863 = empty_worklist env in
                {
                  attempting = (uu___296_21863.attempting);
                  wl_deferred = (uu___296_21863.wl_deferred);
                  ctr = (uu___296_21863.ctr);
                  defer_ok = false;
                  smt_ok = (uu___296_21863.smt_ok);
                  tcenv = (uu___296_21863.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21881  ->
                      match uu____21881 with
                      | (lb,v1) ->
                          let uu____21888 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21888 with
                           | USolved wl1 -> ()
                           | uu____21890 -> fail lb v1))) in
            let rec check_ineq uu____21898 =
              match uu____21898 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21907) -> true
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
                      uu____21930,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21932,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21943) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21950,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21958 -> false) in
            let uu____21963 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21978  ->
                      match uu____21978 with
                      | (u,v1) ->
                          let uu____21985 = check_ineq (u, v1) in
                          if uu____21985
                          then true
                          else
                            ((let uu____21988 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____21988
                              then
                                let uu____21989 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____21990 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____21989
                                  uu____21990
                              else ());
                             false))) in
            if uu____21963
            then ()
            else
              ((let uu____21994 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____21994
                then
                  ((let uu____21996 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21996);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22006 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22006))
                else ());
               (let uu____22016 =
                  let uu____22017 =
                    let uu____22022 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22022) in
                  FStar_Errors.Error uu____22017 in
                FStar_Exn.raise uu____22016))
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
      let fail uu____22070 =
        match uu____22070 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22084 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22084
       then
         let uu____22085 = wl_to_string wl in
         let uu____22086 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22085 uu____22086
       else ());
      (let g1 =
         let uu____22101 = solve_and_commit env wl fail in
         match uu____22101 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___297_22114 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___297_22114.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___297_22114.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___297_22114.FStar_TypeChecker_Env.implicits)
             }
         | uu____22119 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___298_22123 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___298_22123.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___298_22123.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___298_22123.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22145 = FStar_ST.op_Bang last_proof_ns in
    match uu____22145 with
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
            let uu___299_22329 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___299_22329.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___299_22329.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___299_22329.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22330 =
            let uu____22331 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22331 in
          if uu____22330
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22339 = FStar_TypeChecker_Env.get_range env in
                     let uu____22340 =
                       let uu____22341 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22341 in
                     FStar_Errors.diag uu____22339 uu____22340)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22345 = FStar_TypeChecker_Env.get_range env in
                      let uu____22346 =
                        let uu____22347 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22347 in
                      FStar_Errors.diag uu____22345 uu____22346)
                   else ();
                   (let uu____22349 = check_trivial vc1 in
                    match uu____22349 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22356 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22357 =
                                let uu____22358 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22358 in
                              FStar_Errors.diag uu____22356 uu____22357)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22363 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22364 =
                                let uu____22365 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22365 in
                              FStar_Errors.diag uu____22363 uu____22364)
                           else ();
                           (let vcs =
                              let uu____22376 = FStar_Options.use_tactics () in
                              if uu____22376
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22395  ->
                                     (let uu____22397 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22397);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22399 =
                                   let uu____22406 = FStar_Options.peek () in
                                   (env, vc2, uu____22406) in
                                 [uu____22399]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22440  ->
                                    match uu____22440 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22451 = check_trivial goal1 in
                                        (match uu____22451 with
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
                                                (let uu____22459 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22460 =
                                                   let uu____22461 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22462 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22461 uu____22462 in
                                                 FStar_Errors.diag
                                                   uu____22459 uu____22460)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22465 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22466 =
                                                   let uu____22467 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22467 in
                                                 FStar_Errors.diag
                                                   uu____22465 uu____22466)
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
      let uu____22477 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22477 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22483 =
            let uu____22484 =
              let uu____22489 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22489) in
            FStar_Errors.Error uu____22484 in
          FStar_Exn.raise uu____22483
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22496 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22496 with
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
          let uu____22515 = FStar_Syntax_Unionfind.find u in
          match uu____22515 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22518 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22536 = acc in
          match uu____22536 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22622 = hd1 in
                   (match uu____22622 with
                    | (uu____22635,env,u,tm,k,r) ->
                        let uu____22641 = unresolved u in
                        if uu____22641
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22672 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22672
                            then
                              let uu____22673 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22674 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22675 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22673 uu____22674 uu____22675
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___300_22678 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___300_22678.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___300_22678.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___300_22678.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___300_22678.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___300_22678.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___300_22678.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___300_22678.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___300_22678.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___300_22678.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___300_22678.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___300_22678.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___300_22678.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___300_22678.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___300_22678.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___300_22678.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___300_22678.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___300_22678.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___300_22678.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___300_22678.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___300_22678.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___300_22678.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___300_22678.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___300_22678.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___300_22678.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___300_22678.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___300_22678.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___300_22678.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___300_22678.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___300_22678.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___300_22678.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___300_22678.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___300_22678.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___300_22678.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____22681 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___301_22689 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___301_22689.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___301_22689.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___301_22689.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___301_22689.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___301_22689.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___301_22689.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___301_22689.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___301_22689.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___301_22689.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___301_22689.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___301_22689.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___301_22689.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___301_22689.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___301_22689.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___301_22689.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___301_22689.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___301_22689.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___301_22689.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___301_22689.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___301_22689.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___301_22689.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___301_22689.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___301_22689.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___301_22689.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___301_22689.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___301_22689.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___301_22689.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___301_22689.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___301_22689.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___301_22689.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___301_22689.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___301_22689.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.dep_graph =
                                         (uu___301_22689.FStar_TypeChecker_Env.dep_graph)
                                     }) tm1 in
                                match uu____22681 with
                                | (uu____22690,uu____22691,g1) -> g1
                              else
                                (let uu____22694 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___302_22702 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___302_22702.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___302_22702.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___302_22702.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___302_22702.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___302_22702.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___302_22702.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___302_22702.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___302_22702.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___302_22702.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___302_22702.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___302_22702.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___302_22702.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___302_22702.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___302_22702.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___302_22702.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___302_22702.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___302_22702.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___302_22702.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___302_22702.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___302_22702.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___302_22702.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___302_22702.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___302_22702.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___302_22702.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___302_22702.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___302_22702.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___302_22702.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___302_22702.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___302_22702.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___302_22702.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___302_22702.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___302_22702.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___302_22702.FStar_TypeChecker_Env.dep_graph)
                                      }) tm1 in
                                 match uu____22694 with
                                 | (uu____22703,uu____22704,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___303_22707 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___303_22707.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___303_22707.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___303_22707.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____22710 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____22716  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____22710 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___304_22744 = g in
        let uu____22745 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___304_22744.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___304_22744.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___304_22744.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____22745
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
        let uu____22799 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22799 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22812 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22812
      | (reason,uu____22814,uu____22815,e,t,r)::uu____22819 ->
          let uu____22846 =
            let uu____22847 =
              let uu____22852 =
                let uu____22853 = FStar_Syntax_Print.term_to_string t in
                let uu____22854 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22853 uu____22854 in
              (uu____22852, r) in
            FStar_Errors.Error uu____22847 in
          FStar_Exn.raise uu____22846
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___305_22861 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___305_22861.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___305_22861.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___305_22861.FStar_TypeChecker_Env.implicits)
      }
let discharge_guard_nosmt:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun env  ->
    fun g  ->
      let uu____22884 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22884 with
      | FStar_Pervasives_Native.Some uu____22889 -> true
      | FStar_Pervasives_Native.None  -> false
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22899 = try_teq false env t1 t2 in
        match uu____22899 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
let check_subtyping:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____22919 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22919
         then
           let uu____22920 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____22921 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22920
             uu____22921
         else ());
        (let uu____22923 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____22923 with
         | (prob,x) ->
             let g =
               let uu____22939 =
                 let uu____22942 = singleton' env prob true in
                 solve_and_commit env uu____22942
                   (fun uu____22944  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____22939 in
             ((let uu____22954 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____22954
               then
                 let uu____22955 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____22956 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____22957 =
                   let uu____22958 = FStar_Util.must g in
                   guard_to_string env uu____22958 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____22955 uu____22956 uu____22957
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
let get_subtyping_predicate:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22986 = check_subtyping env t1 t2 in
        match uu____22986 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23005 =
              let uu____23006 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____23006 g in
            FStar_Pervasives_Native.Some uu____23005
let get_subtyping_prop:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23018 = check_subtyping env t1 t2 in
        match uu____23018 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23037 =
              let uu____23038 =
                let uu____23039 = FStar_Syntax_Syntax.mk_binder x in
                [uu____23039] in
              close_guard env uu____23038 g in
            FStar_Pervasives_Native.Some uu____23037
let subtype_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23050 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23050
         then
           let uu____23051 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23052 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23051
             uu____23052
         else ());
        (let uu____23054 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23054 with
         | (prob,x) ->
             let g =
               let uu____23064 =
                 let uu____23067 = singleton' env prob false in
                 solve_and_commit env uu____23067
                   (fun uu____23069  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23064 in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23080 =
                      let uu____23081 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____23081] in
                    close_guard env uu____23080 g1 in
                  discharge_guard_nosmt env g2))