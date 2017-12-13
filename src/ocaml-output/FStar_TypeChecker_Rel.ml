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
  'Auu____1438 'Auu____1439 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1439 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1439 ->
              'Auu____1438 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1439,'Auu____1438)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1476 = next_pid () in
                let uu____1477 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1476;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1477;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1491 'Auu____1492 .
    FStar_TypeChecker_Env.env ->
      'Auu____1492 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1492 ->
            'Auu____1491 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1492,'Auu____1491)
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
                let uu____1530 = next_pid () in
                let uu____1531 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1530;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1531;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1544 'Auu____1545 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1545 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1545 ->
            'Auu____1544 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1545,'Auu____1544) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1578 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1578;
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
  'Auu____1584 .
    worklist ->
      ('Auu____1584,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1634 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1634
        then
          let uu____1635 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1636 = prob_to_string env d in
          let uu____1637 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1635 uu____1636 uu____1637 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1643 -> failwith "impossible" in
           let uu____1644 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1658 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1659 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1658, uu____1659)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1665 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1666 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1665, uu____1666) in
           match uu____1644 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___230_1682  ->
            match uu___230_1682 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1694 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1696),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___231_1716  ->
           match uu___231_1716 with
           | UNIV uu____1719 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1725),t) ->
               let uu____1731 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1731
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
        (fun uu___232_1751  ->
           match uu___232_1751 with
           | UNIV (u',t) ->
               let uu____1756 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1756
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1760 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1767 =
        let uu____1768 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1768 in
      FStar_Syntax_Subst.compress uu____1767
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1775 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1775
let norm_arg:
  'Auu____1779 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1779) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1779)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1800 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1800, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1831  ->
              match uu____1831 with
              | (x,imp) ->
                  let uu____1842 =
                    let uu___256_1843 = x in
                    let uu____1844 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___256_1843.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___256_1843.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1844
                    } in
                  (uu____1842, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1859 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1859
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1863 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1863
        | uu____1866 -> u2 in
      let uu____1867 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1867
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
                (let uu____1979 = norm_refinement env t12 in
                 match uu____1979 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____1996;
                     FStar_Syntax_Syntax.vars = uu____1997;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2023 =
                       let uu____2024 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2025 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2024 uu____2025 in
                     failwith uu____2023)
          | FStar_Syntax_Syntax.Tm_uinst uu____2040 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2077 =
                   let uu____2078 = FStar_Syntax_Subst.compress t1' in
                   uu____2078.FStar_Syntax_Syntax.n in
                 match uu____2077 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2095 -> aux true t1'
                 | uu____2102 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2117 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2148 =
                   let uu____2149 = FStar_Syntax_Subst.compress t1' in
                   uu____2149.FStar_Syntax_Syntax.n in
                 match uu____2148 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2166 -> aux true t1'
                 | uu____2173 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2188 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2233 =
                   let uu____2234 = FStar_Syntax_Subst.compress t1' in
                   uu____2234.FStar_Syntax_Syntax.n in
                 match uu____2233 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2251 -> aux true t1'
                 | uu____2258 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2273 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2288 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2303 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2318 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2333 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2360 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2391 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2422 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2449 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2486 ->
              let uu____2493 =
                let uu____2494 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2495 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2494 uu____2495 in
              failwith uu____2493
          | FStar_Syntax_Syntax.Tm_ascribed uu____2510 ->
              let uu____2537 =
                let uu____2538 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2539 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2538 uu____2539 in
              failwith uu____2537
          | FStar_Syntax_Syntax.Tm_delayed uu____2554 ->
              let uu____2579 =
                let uu____2580 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2581 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2580 uu____2581 in
              failwith uu____2579
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2596 =
                let uu____2597 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2598 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2597 uu____2598 in
              failwith uu____2596 in
        let uu____2613 = whnf env t1 in aux false uu____2613
let base_and_refinement:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t
let normalize_refinement:
  'Auu____2635 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2635 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2658 = base_and_refinement env t in
      FStar_All.pipe_right uu____2658 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2692 = FStar_Syntax_Syntax.null_bv t in
    (uu____2692, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2698 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2698 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2719 = base_and_refinement_maybe_delta delta1 env t in
          match uu____2719 with
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
  fun uu____2798  ->
    match uu____2798 with
    | (t_base,refopt) ->
        let uu____2825 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2825 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2857 =
      let uu____2860 =
        let uu____2863 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2886  ->
                  match uu____2886 with | (uu____2893,uu____2894,x) -> x)) in
        FStar_List.append wl.attempting uu____2863 in
      FStar_List.map (wl_prob_to_string wl) uu____2860 in
    FStar_All.pipe_right uu____2857 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2907 =
          let uu____2920 =
            let uu____2921 = FStar_Syntax_Subst.compress k in
            uu____2921.FStar_Syntax_Syntax.n in
          match uu____2920 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2974 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2974)
              else
                (let uu____2988 = FStar_Syntax_Util.abs_formals t in
                 match uu____2988 with
                 | (ys',t1,uu____3011) ->
                     let uu____3016 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3016))
          | uu____3057 ->
              let uu____3058 =
                let uu____3069 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3069) in
              ((ys, t), uu____3058) in
        match uu____2907 with
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
                 let uu____3118 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3118 c in
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
            let uu____3146 = p_guard prob in
            match uu____3146 with
            | (uu____3151,uv) ->
                ((let uu____3154 =
                    let uu____3155 = FStar_Syntax_Subst.compress uv in
                    uu____3155.FStar_Syntax_Syntax.n in
                  match uu____3154 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3187 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3187
                        then
                          let uu____3188 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3189 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3190 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3188
                            uu____3189 uu____3190
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3192 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___257_3195 = wl in
                  {
                    attempting = (uu___257_3195.attempting);
                    wl_deferred = (uu___257_3195.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___257_3195.defer_ok);
                    smt_ok = (uu___257_3195.smt_ok);
                    tcenv = (uu___257_3195.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3210 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3210
         then
           let uu____3211 = FStar_Util.string_of_int pid in
           let uu____3212 =
             let uu____3213 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3213 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3211 uu____3212
         else ());
        commit sol;
        (let uu___258_3220 = wl in
         {
           attempting = (uu___258_3220.attempting);
           wl_deferred = (uu___258_3220.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___258_3220.defer_ok);
           smt_ok = (uu___258_3220.smt_ok);
           tcenv = (uu___258_3220.tcenv)
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
            | (uu____3258,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3270 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3270 in
          (let uu____3276 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3276
           then
             let uu____3277 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3278 =
               let uu____3279 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3279 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3277 uu____3278
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
        let uu____3311 =
          let uu____3318 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3318 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3311
          (FStar_Util.for_some
             (fun uu____3354  ->
                match uu____3354 with
                | (uv,uu____3360) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3367 'Auu____3368 .
    'Auu____3368 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3367)
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
            let uu____3400 = occurs wl uk t in Prims.op_Negation uu____3400 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3407 =
                 let uu____3408 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3409 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3408 uu____3409 in
               FStar_Pervasives_Native.Some uu____3407) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3419 'Auu____3420 .
    'Auu____3420 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3419)
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
            let uu____3474 = occurs_check env wl uk t in
            match uu____3474 with
            | (occurs_ok,msg) ->
                let uu____3505 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3505, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3528 'Auu____3529 .
    (FStar_Syntax_Syntax.bv,'Auu____3529) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3528) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3528) FStar_Pervasives_Native.tuple2
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
      let uu____3613 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3667  ->
                fun uu____3668  ->
                  match (uu____3667, uu____3668) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3749 =
                        let uu____3750 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3750 in
                      if uu____3749
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3775 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3775
                         then
                           let uu____3788 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3788)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3613 with | (isect,uu____3829) -> FStar_List.rev isect
let binders_eq:
  'Auu____3854 'Auu____3855 .
    (FStar_Syntax_Syntax.bv,'Auu____3855) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3854) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3910  ->
              fun uu____3911  ->
                match (uu____3910, uu____3911) with
                | ((a,uu____3929),(b,uu____3931)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3945 'Auu____3946 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3946) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3945)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3945)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____3997 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4011  ->
                      match uu____4011 with
                      | (b,uu____4017) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____3997
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4033 -> FStar_Pervasives_Native.None
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
            let uu____4106 = pat_var_opt env seen hd1 in
            (match uu____4106 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4120 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4120
                   then
                     let uu____4121 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4121
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4139 =
      let uu____4140 = FStar_Syntax_Subst.compress t in
      uu____4140.FStar_Syntax_Syntax.n in
    match uu____4139 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4143 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4160;
           FStar_Syntax_Syntax.pos = uu____4161;
           FStar_Syntax_Syntax.vars = uu____4162;_},uu____4163)
        -> true
    | uu____4200 -> false
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
           FStar_Syntax_Syntax.pos = uu____4324;
           FStar_Syntax_Syntax.vars = uu____4325;_},args)
        -> (t, uv, k, args)
    | uu____4393 -> failwith "Not a flex-uvar"
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
      let uu____4470 = destruct_flex_t t in
      match uu____4470 with
      | (t1,uv,k,args) ->
          let uu____4585 = pat_vars env [] args in
          (match uu____4585 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4683 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4764 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4799 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4803 -> false
let head_match: match_result -> match_result =
  fun uu___233_4806  ->
    match uu___233_4806 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4821 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4830 ->
          let uu____4831 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4831 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4842 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4861 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4870 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4897 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4898 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4899 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4916 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4929 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4953) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4959,uu____4960) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5002) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5023;
             FStar_Syntax_Syntax.index = uu____5024;
             FStar_Syntax_Syntax.sort = t2;_},uu____5026)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5033 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5034 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5035 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5048 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5066 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5066
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
            let uu____5087 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5087
            then FullMatch
            else
              (let uu____5089 =
                 let uu____5098 =
                   let uu____5101 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5101 in
                 let uu____5102 =
                   let uu____5105 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5105 in
                 (uu____5098, uu____5102) in
               MisMatch uu____5089)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5111),FStar_Syntax_Syntax.Tm_uinst (g,uu____5113)) ->
            let uu____5122 = head_matches env f g in
            FStar_All.pipe_right uu____5122 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5125 = FStar_Const.eq_const c d in
            if uu____5125
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5132),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5134)) ->
            let uu____5183 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5183
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5190),FStar_Syntax_Syntax.Tm_refine (y,uu____5192)) ->
            let uu____5201 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5201 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5203),uu____5204) ->
            let uu____5209 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5209 head_match
        | (uu____5210,FStar_Syntax_Syntax.Tm_refine (x,uu____5212)) ->
            let uu____5217 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5217 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5218,FStar_Syntax_Syntax.Tm_type
           uu____5219) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5220,FStar_Syntax_Syntax.Tm_arrow uu____5221) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5247),FStar_Syntax_Syntax.Tm_app (head',uu____5249))
            ->
            let uu____5290 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5290 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5292),uu____5293) ->
            let uu____5314 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5314 head_match
        | (uu____5315,FStar_Syntax_Syntax.Tm_app (head1,uu____5317)) ->
            let uu____5338 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5338 head_match
        | uu____5339 ->
            let uu____5344 =
              let uu____5353 = delta_depth_of_term env t11 in
              let uu____5356 = delta_depth_of_term env t21 in
              (uu____5353, uu____5356) in
            MisMatch uu____5344
let head_matches_delta:
  'Auu____5368 .
    FStar_TypeChecker_Env.env ->
      'Auu____5368 ->
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
            let uu____5401 = FStar_Syntax_Util.head_and_args t in
            match uu____5401 with
            | (head1,uu____5419) ->
                let uu____5440 =
                  let uu____5441 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5441.FStar_Syntax_Syntax.n in
                (match uu____5440 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5447 =
                       let uu____5448 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5448 FStar_Option.isSome in
                     if uu____5447
                     then
                       let uu____5467 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5467
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5471 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5574)
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
                (uu____5641,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5659 =
                     let uu____5668 = maybe_inline t11 in
                     let uu____5671 = maybe_inline t21 in
                     (uu____5668, uu____5671) in
                   match uu____5659 with
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
                let uu____5714 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5714 with
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
                let uu____5737 =
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
                (match uu____5737 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5761 -> fail r
            | uu____5770 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5803 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____5839 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___234_5851  ->
    match uu___234_5851 with
    | T (t,uu____5853) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5869 = FStar_Syntax_Util.type_u () in
      match uu____5869 with
      | (t,uu____5875) ->
          let uu____5876 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____5876
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5887 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____5887 FStar_Pervasives_Native.fst
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
        let uu____5951 = head_matches env t1 t' in
        match uu____5951 with
        | MisMatch uu____5952 -> false
        | uu____5961 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6057,imp),T (t2,uu____6060)) -> (t2, imp)
                     | uu____6079 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6146  ->
                    match uu____6146 with
                    | (t2,uu____6160) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6203 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6203 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6278))::tcs2) ->
                       aux
                         (((let uu___259_6313 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___259_6313.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___259_6313.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6331 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___235_6384 =
                 match uu___235_6384 with
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
               let uu____6501 = decompose1 [] bs1 in
               (rebuild, matches, uu____6501))
      | uu____6550 ->
          let rebuild uu___236_6556 =
            match uu___236_6556 with
            | [] -> t1
            | uu____6559 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___237_6590  ->
    match uu___237_6590 with
    | T (t,uu____6592) -> t
    | uu____6601 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___238_6604  ->
    match uu___238_6604 with
    | T (t,uu____6606) -> FStar_Syntax_Syntax.as_arg t
    | uu____6615 -> failwith "Impossible"
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
              | (uu____6721,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6746 = new_uvar r scope1 k in
                  (match uu____6746 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6764 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6781 =
                         let uu____6782 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6782 in
                       ((T (gi_xs, mk_kind)), uu____6781))
              | (uu____6795,uu____6796,C uu____6797) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____6944 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6961;
                         FStar_Syntax_Syntax.vars = uu____6962;_})
                        ->
                        let uu____6985 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6985 with
                         | (T (gi_xs,uu____7009),prob) ->
                             let uu____7019 =
                               let uu____7020 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7020 in
                             (uu____7019, [prob])
                         | uu____7023 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7038;
                         FStar_Syntax_Syntax.vars = uu____7039;_})
                        ->
                        let uu____7062 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7062 with
                         | (T (gi_xs,uu____7086),prob) ->
                             let uu____7096 =
                               let uu____7097 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7097 in
                             (uu____7096, [prob])
                         | uu____7100 -> failwith "impossible")
                    | (uu____7111,uu____7112,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7114;
                         FStar_Syntax_Syntax.vars = uu____7115;_})
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
                        let uu____7246 =
                          let uu____7255 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7255 FStar_List.unzip in
                        (match uu____7246 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7309 =
                                 let uu____7310 =
                                   let uu____7313 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7313 un_T in
                                 let uu____7314 =
                                   let uu____7323 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7323
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7310;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7314;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7309 in
                             ((C gi_xs), sub_probs))
                    | uu____7332 ->
                        let uu____7345 = sub_prob scope1 args q in
                        (match uu____7345 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____6944 with
                   | (tc,probs) ->
                       let uu____7376 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7439,uu____7440),T
                            (t,uu____7442)) ->
                             let b1 =
                               ((let uu___260_7479 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___260_7479.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___260_7479.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7480 =
                               let uu____7487 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7487 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7480)
                         | uu____7522 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7376 with
                        | (bopt,scope2,args1) ->
                            let uu____7606 = aux scope2 args1 qs2 in
                            (match uu____7606 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7643 =
                                         let uu____7646 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7646 in
                                       FStar_Syntax_Util.mk_conj_l uu____7643
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7669 =
                                         let uu____7672 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7673 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7672 :: uu____7673 in
                                       FStar_Syntax_Util.mk_conj_l uu____7669 in
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
  'Auu____7741 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7741)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7741)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___261_7762 = p in
      let uu____7767 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7768 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___261_7762.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7767;
        FStar_TypeChecker_Common.relation =
          (uu___261_7762.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7768;
        FStar_TypeChecker_Common.element =
          (uu___261_7762.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___261_7762.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___261_7762.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___261_7762.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___261_7762.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___261_7762.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7780 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7780
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7789 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____7809 = compress_prob wl pr in
        FStar_All.pipe_right uu____7809 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7819 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____7819 with
           | (lh,uu____7839) ->
               let uu____7860 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____7860 with
                | (rh,uu____7880) ->
                    let uu____7901 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7918,FStar_Syntax_Syntax.Tm_uvar uu____7919)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7956,uu____7957)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____7978,FStar_Syntax_Syntax.Tm_uvar uu____7979)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8000,uu____8001)
                          ->
                          let uu____8018 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8018 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8067 ->
                                    let rank =
                                      let uu____8075 = is_top_level_prob prob in
                                      if uu____8075
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8077 =
                                      let uu___262_8082 = tp in
                                      let uu____8087 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___262_8082.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___262_8082.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___262_8082.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8087;
                                        FStar_TypeChecker_Common.element =
                                          (uu___262_8082.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___262_8082.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___262_8082.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___262_8082.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___262_8082.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___262_8082.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8077)))
                      | (uu____8098,FStar_Syntax_Syntax.Tm_uvar uu____8099)
                          ->
                          let uu____8116 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8116 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8165 ->
                                    let uu____8172 =
                                      let uu___263_8179 = tp in
                                      let uu____8184 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___263_8179.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8184;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___263_8179.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___263_8179.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___263_8179.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___263_8179.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___263_8179.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___263_8179.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___263_8179.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___263_8179.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8172)))
                      | (uu____8201,uu____8202) -> (rigid_rigid, tp) in
                    (match uu____7901 with
                     | (rank,tp1) ->
                         let uu____8221 =
                           FStar_All.pipe_right
                             (let uu___264_8227 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___264_8227.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___264_8227.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___264_8227.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___264_8227.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___264_8227.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___264_8227.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___264_8227.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___264_8227.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___264_8227.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8221))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8237 =
            FStar_All.pipe_right
              (let uu___265_8243 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___265_8243.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___265_8243.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___265_8243.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___265_8243.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___265_8243.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___265_8243.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___265_8243.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___265_8243.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___265_8243.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8237)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8298 probs =
      match uu____8298 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8351 = rank wl hd1 in
               (match uu____8351 with
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
    match projectee with | UDeferred _0 -> true | uu____8458 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8470 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8482 -> false
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
                        let uu____8522 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8522 with
                        | (k,uu____8528) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8538 -> false)))
            | uu____8539 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8590 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8590 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8593 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8603 =
                     let uu____8604 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8605 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8604
                       uu____8605 in
                   UFailed uu____8603)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8625 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8625 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8647 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8647 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8650 ->
                let uu____8655 =
                  let uu____8656 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8657 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8656
                    uu____8657 msg in
                UFailed uu____8655 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8658,uu____8659) ->
              let uu____8660 =
                let uu____8661 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8662 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8661 uu____8662 in
              failwith uu____8660
          | (FStar_Syntax_Syntax.U_unknown ,uu____8663) ->
              let uu____8664 =
                let uu____8665 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8666 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8665 uu____8666 in
              failwith uu____8664
          | (uu____8667,FStar_Syntax_Syntax.U_bvar uu____8668) ->
              let uu____8669 =
                let uu____8670 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8671 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8670 uu____8671 in
              failwith uu____8669
          | (uu____8672,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8673 =
                let uu____8674 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8675 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8674 uu____8675 in
              failwith uu____8673
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8699 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8699
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8721 = occurs_univ v1 u3 in
              if uu____8721
              then
                let uu____8722 =
                  let uu____8723 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8724 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8723 uu____8724 in
                try_umax_components u11 u21 uu____8722
              else
                (let uu____8726 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8726)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8746 = occurs_univ v1 u3 in
              if uu____8746
              then
                let uu____8747 =
                  let uu____8748 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8749 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8748 uu____8749 in
                try_umax_components u11 u21 uu____8747
              else
                (let uu____8751 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8751)
          | (FStar_Syntax_Syntax.U_max uu____8760,uu____8761) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8767 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8767
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8769,FStar_Syntax_Syntax.U_max uu____8770) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8776 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8776
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8778,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8779,FStar_Syntax_Syntax.U_name
             uu____8780) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8781) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8782) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8783,FStar_Syntax_Syntax.U_succ
             uu____8784) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8785,FStar_Syntax_Syntax.U_zero
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
      let uu____8871 = bc1 in
      match uu____8871 with
      | (bs1,mk_cod1) ->
          let uu____8912 = bc2 in
          (match uu____8912 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____8982 = FStar_Util.first_N n1 bs in
                 match uu____8982 with
                 | (bs3,rest) ->
                     let uu____9007 = mk_cod rest in (bs3, uu____9007) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9036 =
                   let uu____9043 = mk_cod1 [] in (bs1, uu____9043) in
                 let uu____9046 =
                   let uu____9053 = mk_cod2 [] in (bs2, uu____9053) in
                 (uu____9036, uu____9046)
               else
                 if l1 > l2
                 then
                   (let uu____9095 = curry l2 bs1 mk_cod1 in
                    let uu____9108 =
                      let uu____9115 = mk_cod2 [] in (bs2, uu____9115) in
                    (uu____9095, uu____9108))
                 else
                   (let uu____9131 =
                      let uu____9138 = mk_cod1 [] in (bs1, uu____9138) in
                    let uu____9141 = curry l1 bs2 mk_cod2 in
                    (uu____9131, uu____9141)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9262 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9262
       then
         let uu____9263 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9263
       else ());
      (let uu____9265 = next_prob probs in
       match uu____9265 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___266_9286 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___266_9286.wl_deferred);
               ctr = (uu___266_9286.ctr);
               defer_ok = (uu___266_9286.defer_ok);
               smt_ok = (uu___266_9286.smt_ok);
               tcenv = (uu___266_9286.tcenv)
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
                  let uu____9297 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9297 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9302 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9302 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9307,uu____9308) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9325 ->
                let uu____9334 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9393  ->
                          match uu____9393 with
                          | (c,uu____9401,uu____9402) -> c < probs.ctr)) in
                (match uu____9334 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9443 =
                            FStar_List.map
                              (fun uu____9458  ->
                                 match uu____9458 with
                                 | (uu____9469,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9443
                      | uu____9472 ->
                          let uu____9481 =
                            let uu___267_9482 = probs in
                            let uu____9483 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9504  ->
                                      match uu____9504 with
                                      | (uu____9511,uu____9512,y) -> y)) in
                            {
                              attempting = uu____9483;
                              wl_deferred = rest;
                              ctr = (uu___267_9482.ctr);
                              defer_ok = (uu___267_9482.defer_ok);
                              smt_ok = (uu___267_9482.smt_ok);
                              tcenv = (uu___267_9482.tcenv)
                            } in
                          solve env uu____9481))))
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
            let uu____9519 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9519 with
            | USolved wl1 ->
                let uu____9521 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9521
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
                  let uu____9567 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9567 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9570 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9582;
                  FStar_Syntax_Syntax.vars = uu____9583;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9586;
                  FStar_Syntax_Syntax.vars = uu____9587;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9601,uu____9602) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9609,FStar_Syntax_Syntax.Tm_uinst uu____9610) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9617 -> USolved wl
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
            ((let uu____9627 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9627
              then
                let uu____9628 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9628 msg
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
        (let uu____9637 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9637
         then
           let uu____9638 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9638
         else ());
        (let uu____9640 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9640 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9702 = head_matches_delta env () t1 t2 in
               match uu____9702 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9743 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____9792 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9807 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____9808 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____9807, uu____9808)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9813 = FStar_Syntax_Subst.compress t1 in
                              let uu____9814 = FStar_Syntax_Subst.compress t2 in
                              (uu____9813, uu____9814) in
                        (match uu____9792 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____9840 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____9840 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____9871 =
                                    let uu____9880 =
                                      let uu____9883 =
                                        let uu____9886 =
                                          let uu____9887 =
                                            let uu____9894 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____9894) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____9887 in
                                        FStar_Syntax_Syntax.mk uu____9886 in
                                      uu____9883 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____9902 =
                                      let uu____9905 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____9905] in
                                    (uu____9880, uu____9902) in
                                  FStar_Pervasives_Native.Some uu____9871
                              | (uu____9918,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9920)) ->
                                  let uu____9925 =
                                    let uu____9932 =
                                      let uu____9935 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____9935] in
                                    (t11, uu____9932) in
                                  FStar_Pervasives_Native.Some uu____9925
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9945),uu____9946) ->
                                  let uu____9951 =
                                    let uu____9958 =
                                      let uu____9961 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____9961] in
                                    (t21, uu____9958) in
                                  FStar_Pervasives_Native.Some uu____9951
                              | uu____9970 ->
                                  let uu____9975 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____9975 with
                                   | (head1,uu____9999) ->
                                       let uu____10020 =
                                         let uu____10021 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10021.FStar_Syntax_Syntax.n in
                                       (match uu____10020 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10032;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10034;_}
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
                                        | uu____10041 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10054) ->
                  let uu____10079 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___239_10105  ->
                            match uu___239_10105 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10112 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10112 with
                                      | (u',uu____10128) ->
                                          let uu____10149 =
                                            let uu____10150 = whnf env u' in
                                            uu____10150.FStar_Syntax_Syntax.n in
                                          (match uu____10149 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10154) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10179 -> false))
                                 | uu____10180 -> false)
                            | uu____10183 -> false)) in
                  (match uu____10079 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10217 tps =
                         match uu____10217 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10265 =
                                    let uu____10274 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10274 in
                                  (match uu____10265 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10309 -> FStar_Pervasives_Native.None) in
                       let uu____10318 =
                         let uu____10327 =
                           let uu____10334 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10334, []) in
                         make_lower_bound uu____10327 lower_bounds in
                       (match uu____10318 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10346 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10346
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
                            ((let uu____10366 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10366
                              then
                                let wl' =
                                  let uu___268_10368 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___268_10368.wl_deferred);
                                    ctr = (uu___268_10368.ctr);
                                    defer_ok = (uu___268_10368.defer_ok);
                                    smt_ok = (uu___268_10368.smt_ok);
                                    tcenv = (uu___268_10368.tcenv)
                                  } in
                                let uu____10369 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10369
                              else ());
                             (let uu____10371 =
                                solve_t env eq_prob
                                  (let uu___269_10373 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___269_10373.wl_deferred);
                                     ctr = (uu___269_10373.ctr);
                                     defer_ok = (uu___269_10373.defer_ok);
                                     smt_ok = (uu___269_10373.smt_ok);
                                     tcenv = (uu___269_10373.tcenv)
                                   }) in
                              match uu____10371 with
                              | Success uu____10376 ->
                                  let wl1 =
                                    let uu___270_10378 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___270_10378.wl_deferred);
                                      ctr = (uu___270_10378.ctr);
                                      defer_ok = (uu___270_10378.defer_ok);
                                      smt_ok = (uu___270_10378.smt_ok);
                                      tcenv = (uu___270_10378.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10380 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10385 -> FStar_Pervasives_Native.None))))
              | uu____10386 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10395 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10395
         then
           let uu____10396 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10396
         else ());
        (let uu____10398 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10398 with
         | (u,args) ->
             let uu____10437 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10437 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10478 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10478 with
                    | (h1,args1) ->
                        let uu____10519 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10519 with
                         | (h2,uu____10539) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10566 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10566
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10584 =
                                          let uu____10587 =
                                            let uu____10588 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10588 in
                                          [uu____10587] in
                                        FStar_Pervasives_Native.Some
                                          uu____10584))
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
                                       (let uu____10621 =
                                          let uu____10624 =
                                            let uu____10625 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10625 in
                                          [uu____10624] in
                                        FStar_Pervasives_Native.Some
                                          uu____10621))
                                  else FStar_Pervasives_Native.None
                              | uu____10639 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10729 =
                               let uu____10738 =
                                 let uu____10741 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10741 in
                               (uu____10738, m1) in
                             FStar_Pervasives_Native.Some uu____10729)
                    | (uu____10754,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10756)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____10804),uu____10805) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____10852 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10905) ->
                       let uu____10930 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___240_10956  ->
                                 match uu___240_10956 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____10963 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____10963 with
                                           | (u',uu____10979) ->
                                               let uu____11000 =
                                                 let uu____11001 =
                                                   whnf env u' in
                                                 uu____11001.FStar_Syntax_Syntax.n in
                                               (match uu____11000 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11005) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11030 -> false))
                                      | uu____11031 -> false)
                                 | uu____11034 -> false)) in
                       (match uu____10930 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11072 tps =
                              match uu____11072 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11134 =
                                         let uu____11145 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11145 in
                                       (match uu____11134 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11196 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11207 =
                              let uu____11218 =
                                let uu____11227 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11227, []) in
                              make_upper_bound uu____11218 upper_bounds in
                            (match uu____11207 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11241 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11241
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
                                 ((let uu____11267 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11267
                                   then
                                     let wl' =
                                       let uu___271_11269 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___271_11269.wl_deferred);
                                         ctr = (uu___271_11269.ctr);
                                         defer_ok = (uu___271_11269.defer_ok);
                                         smt_ok = (uu___271_11269.smt_ok);
                                         tcenv = (uu___271_11269.tcenv)
                                       } in
                                     let uu____11270 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11270
                                   else ());
                                  (let uu____11272 =
                                     solve_t env eq_prob
                                       (let uu___272_11274 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___272_11274.wl_deferred);
                                          ctr = (uu___272_11274.ctr);
                                          defer_ok =
                                            (uu___272_11274.defer_ok);
                                          smt_ok = (uu___272_11274.smt_ok);
                                          tcenv = (uu___272_11274.tcenv)
                                        }) in
                                   match uu____11272 with
                                   | Success uu____11277 ->
                                       let wl1 =
                                         let uu___273_11279 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___273_11279.wl_deferred);
                                           ctr = (uu___273_11279.ctr);
                                           defer_ok =
                                             (uu___273_11279.defer_ok);
                                           smt_ok = (uu___273_11279.smt_ok);
                                           tcenv = (uu___273_11279.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11281 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11286 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11287 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11362 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11362
                      then
                        let uu____11363 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11363
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___274_11417 = hd1 in
                      let uu____11418 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___274_11417.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___274_11417.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11418
                      } in
                    let hd21 =
                      let uu___275_11422 = hd2 in
                      let uu____11423 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___275_11422.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___275_11422.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11423
                      } in
                    let prob =
                      let uu____11427 =
                        let uu____11432 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11432 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11427 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11443 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11443 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11447 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11447 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11485 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11490 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11485 uu____11490 in
                         ((let uu____11500 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11500
                           then
                             let uu____11501 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11502 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11501 uu____11502
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11525 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11535 = aux scope env [] bs1 bs2 in
              match uu____11535 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11559 = compress_tprob wl problem in
        solve_t' env uu____11559 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11592 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11592 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11623,uu____11624) ->
                   let rec may_relate head3 =
                     let uu____11649 =
                       let uu____11650 = FStar_Syntax_Subst.compress head3 in
                       uu____11650.FStar_Syntax_Syntax.n in
                     match uu____11649 with
                     | FStar_Syntax_Syntax.Tm_name uu____11653 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11654 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11677;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11678;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11681;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11682;
                           FStar_Syntax_Syntax.fv_qual = uu____11683;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11687,uu____11688) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11730) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11736) ->
                         may_relate t
                     | uu____11741 -> false in
                   let uu____11742 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11742
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
                                let uu____11759 =
                                  let uu____11760 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11760 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11759 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11762 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11762
                   else
                     (let uu____11764 =
                        let uu____11765 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11766 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11765 uu____11766 in
                      giveup env1 uu____11764 orig)
               | (uu____11767,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___276_11781 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___276_11781.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___276_11781.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___276_11781.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___276_11781.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___276_11781.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___276_11781.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___276_11781.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___276_11781.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____11782,FStar_Pervasives_Native.None ) ->
                   ((let uu____11794 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____11794
                     then
                       let uu____11795 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11796 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____11797 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____11798 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____11795
                         uu____11796 uu____11797 uu____11798
                     else ());
                    (let uu____11800 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____11800 with
                     | (head11,args1) ->
                         let uu____11837 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____11837 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____11891 =
                                  let uu____11892 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____11893 = args_to_string args1 in
                                  let uu____11894 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____11895 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____11892 uu____11893 uu____11894
                                    uu____11895 in
                                giveup env1 uu____11891 orig
                              else
                                (let uu____11897 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____11903 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____11903 = FStar_Syntax_Util.Equal) in
                                 if uu____11897
                                 then
                                   let uu____11904 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____11904 with
                                   | USolved wl2 ->
                                       let uu____11906 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____11906
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____11910 =
                                      base_and_refinement env1 t1 in
                                    match uu____11910 with
                                    | (base1,refinement1) ->
                                        let uu____11935 =
                                          base_and_refinement env1 t2 in
                                        (match uu____11935 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____11992 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____11992 with
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
                                                           (fun uu____12014 
                                                              ->
                                                              fun uu____12015
                                                                 ->
                                                                match 
                                                                  (uu____12014,
                                                                    uu____12015)
                                                                with
                                                                | ((a,uu____12033),
                                                                   (a',uu____12035))
                                                                    ->
                                                                    let uu____12044
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
                                                                    uu____12044)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12054 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12054 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12060 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___277_12096 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___277_12096.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12129 =
          match uu____12129 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12171 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu____12171 then f () else () in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12267  ->
                     let uu____12268 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12268);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12336  ->
                               match uu____12336 with
                               | (x,imp) ->
                                   let uu____12347 =
                                     FStar_Syntax_Syntax.bv_to_name x in
                                   (uu____12347, imp))) in
                     let pattern_vars1 = FStar_List.rev pattern_vars in
                     let kk =
                       let uu____12360 = FStar_Syntax_Util.type_u () in
                       match uu____12360 with
                       | (t1,uu____12366) ->
                           let uu____12367 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1 in
                           FStar_Pervasives_Native.fst uu____12367 in
                     let uu____12372 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                     (match uu____12372 with
                      | (t',tm_u1) ->
                          let uu____12385 = destruct_flex_t t' in
                          (match uu____12385 with
                           | (uu____12422,u1,k1,uu____12425) ->
                               let all_formals = FStar_List.rev seen_formals in
                               let k2 =
                                 let uu____12484 =
                                   FStar_Syntax_Syntax.mk_Total res_t in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____12484 in
                               let sol =
                                 let uu____12488 =
                                   let uu____12497 = u_abs k2 all_formals t' in
                                   ((u, k2), uu____12497) in
                                 TERM uu____12488 in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____12632  ->
                           let uu____12633 =
                             FStar_Syntax_Print.binder_to_string formal in
                           let uu____12634 =
                             FStar_Syntax_Print.args_to_string [hd1] in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____12633 uu____12634);
                      (let uu____12647 = pat_var_opt env pat_args hd1 in
                       match uu____12647 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____12667  ->
                                 FStar_Util.print_string
                                   "not a pattern var\n");
                            aux pat_args pat_args_set pattern_vars
                              pattern_var_set (formal :: seen_formals)
                              formals1 res_t tl1)
                       | FStar_Pervasives_Native.Some y ->
                           let maybe_pat =
                             match xs_opt with
                             | FStar_Pervasives_Native.None  -> true
                             | FStar_Pervasives_Native.Some xs ->
                                 FStar_All.pipe_right xs
                                   (FStar_Util.for_some
                                      (fun uu____12710  ->
                                         match uu____12710 with
                                         | (x,uu____12716) ->
                                             FStar_Syntax_Syntax.bv_eq x
                                               (FStar_Pervasives_Native.fst y))) in
                           if Prims.op_Negation maybe_pat
                           then
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1
                           else
                             (debug1
                                (fun uu____12731  ->
                                   let uu____12732 =
                                     FStar_Syntax_Print.args_to_string [hd1] in
                                   let uu____12745 =
                                     FStar_Syntax_Print.binder_to_string y in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____12732
                                     uu____12745);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                               let uu____12749 =
                                 let uu____12750 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set in
                                 Prims.op_Negation uu____12750 in
                               if uu____12749
                               then
                                 (debug1
                                    (fun uu____12762  ->
                                       let uu____12763 =
                                         let uu____12766 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1] in
                                         let uu____12779 =
                                           let uu____12782 =
                                             FStar_Syntax_Print.binder_to_string
                                               y in
                                           let uu____12783 =
                                             let uu____12786 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort in
                                             let uu____12787 =
                                               let uu____12790 =
                                                 names_to_string fvs in
                                               let uu____12791 =
                                                 let uu____12794 =
                                                   names_to_string
                                                     pattern_var_set in
                                                 [uu____12794] in
                                               uu____12790 :: uu____12791 in
                                             uu____12786 :: uu____12787 in
                                           uu____12782 :: uu____12783 in
                                         uu____12766 :: uu____12779 in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____12763);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____12796 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set in
                                  let uu____12799 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set in
                                  aux (y :: pat_args) uu____12796 (formal ::
                                    pattern_vars) uu____12799 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____12806::uu____12807) ->
                     let uu____12838 =
                       let uu____12851 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                       FStar_Syntax_Util.arrow_formals uu____12851 in
                     (match uu____12838 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____12890 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____12897::uu____12898,[]) ->
                     FStar_Pervasives_Native.None) in
              let uu____12921 =
                let uu____12934 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____12934 in
              (match uu____12921 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____12970  ->
                         let uu____12971 =
                           FStar_Syntax_Print.term_to_string t in
                         let uu____12972 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals in
                         let uu____12973 =
                           FStar_Syntax_Print.term_to_string res_t in
                         let uu____12974 =
                           FStar_Syntax_Print.args_to_string args in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____12971 uu____12972 uu____12973 uu____12974);
                    (let uu____12975 = FStar_Syntax_Syntax.new_bv_set () in
                     let uu____12978 = FStar_Syntax_Syntax.new_bv_set () in
                     aux [] uu____12975 [] uu____12978 [] all_formals res_t
                       args))) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13012 = lhs in
          match uu____13012 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13022 ->
                    let uu____13023 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13023 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13046 = p in
          match uu____13046 with
          | (((u,k),xs,c),ps,(h,uu____13057,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13139 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13139 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13162 = h gs_xs in
                     let uu____13163 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13162 uu____13163 in
                   ((let uu____13169 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13169
                     then
                       let uu____13170 =
                         let uu____13173 =
                           let uu____13174 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13174
                             (FStar_String.concat "\n\t>") in
                         let uu____13179 =
                           let uu____13182 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13183 =
                             let uu____13186 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13187 =
                               let uu____13190 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13191 =
                                 let uu____13194 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13195 =
                                   let uu____13198 =
                                     let uu____13199 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13199
                                       (FStar_String.concat ", ") in
                                   let uu____13204 =
                                     let uu____13207 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13207] in
                                   uu____13198 :: uu____13204 in
                                 uu____13194 :: uu____13195 in
                               uu____13190 :: uu____13191 in
                             uu____13186 :: uu____13187 in
                           uu____13182 :: uu____13183 in
                         uu____13173 :: uu____13179 in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13170
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___241_13228 =
          match uu___241_13228 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13260 = p in
          match uu____13260 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13351 = FStar_List.nth ps i in
              (match uu____13351 with
               | (pi,uu____13355) ->
                   let uu____13360 = FStar_List.nth xs i in
                   (match uu____13360 with
                    | (xi,uu____13372) ->
                        let rec gs k =
                          let uu____13385 =
                            let uu____13398 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13398 in
                          match uu____13385 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13473)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13486 = new_uvar r xs k_a in
                                    (match uu____13486 with
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
                                         let uu____13508 = aux subst2 tl1 in
                                         (match uu____13508 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13535 =
                                                let uu____13538 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13538 :: gi_xs' in
                                              let uu____13539 =
                                                let uu____13542 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13542 :: gi_ps' in
                                              (uu____13535, uu____13539))) in
                              aux [] bs in
                        let uu____13547 =
                          let uu____13548 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13548 in
                        if uu____13547
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13552 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13552 with
                           | (g_xs,uu____13564) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13575 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13576 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13575
                                   uu____13576 in
                               let sub1 =
                                 let uu____13582 =
                                   let uu____13587 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13590 =
                                     let uu____13593 =
                                       FStar_List.map
                                         (fun uu____13608  ->
                                            match uu____13608 with
                                            | (uu____13617,uu____13618,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13593 in
                                   mk_problem (p_scope orig) orig uu____13587
                                     (p_rel orig) uu____13590
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13582 in
                               ((let uu____13633 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13633
                                 then
                                   let uu____13634 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13635 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13634 uu____13635
                                 else ());
                                (let wl2 =
                                   let uu____13638 =
                                     let uu____13641 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13641 in
                                   solve_prob orig uu____13638
                                     [TERM (u, proj)] wl1 in
                                 let uu____13650 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13650))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13681 = lhs in
          match uu____13681 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13717 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13717 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13750 =
                        let uu____13797 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13797) in
                      FStar_Pervasives_Native.Some uu____13750
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____13941 =
                           let uu____13948 =
                             let uu____13949 = FStar_Syntax_Subst.compress k1 in
                             uu____13949.FStar_Syntax_Syntax.n in
                           (uu____13948, args) in
                         match uu____13941 with
                         | (uu____13960,[]) ->
                             let uu____13963 =
                               let uu____13974 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____13974) in
                             FStar_Pervasives_Native.Some uu____13963
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13995,uu____13996) ->
                             let uu____14017 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14017 with
                              | (uv1,uv_args) ->
                                  let uu____14060 =
                                    let uu____14061 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14061.FStar_Syntax_Syntax.n in
                                  (match uu____14060 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14071) ->
                                       let uu____14096 =
                                         pat_vars env [] uv_args in
                                       (match uu____14096 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14123  ->
                                                      let uu____14124 =
                                                        let uu____14125 =
                                                          let uu____14126 =
                                                            let uu____14131 =
                                                              let uu____14132
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14132
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14131 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14126 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14125 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14124)) in
                                            let c1 =
                                              let uu____14142 =
                                                let uu____14143 =
                                                  let uu____14148 =
                                                    let uu____14149 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14149
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14148 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14143 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14142 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14162 =
                                                let uu____14165 =
                                                  let uu____14166 =
                                                    let uu____14169 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14169
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14166 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14165 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14162 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14187 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14192,uu____14193) ->
                             let uu____14212 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14212 with
                              | (uv1,uv_args) ->
                                  let uu____14255 =
                                    let uu____14256 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14256.FStar_Syntax_Syntax.n in
                                  (match uu____14255 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14266) ->
                                       let uu____14291 =
                                         pat_vars env [] uv_args in
                                       (match uu____14291 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14318  ->
                                                      let uu____14319 =
                                                        let uu____14320 =
                                                          let uu____14321 =
                                                            let uu____14326 =
                                                              let uu____14327
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14327
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14326 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14321 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14320 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14319)) in
                                            let c1 =
                                              let uu____14337 =
                                                let uu____14338 =
                                                  let uu____14343 =
                                                    let uu____14344 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14344
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14343 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14338 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14337 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14357 =
                                                let uu____14360 =
                                                  let uu____14361 =
                                                    let uu____14364 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14364
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14361 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14360 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14357 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14382 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14389) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14430 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14430
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14466 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14466 with
                                  | (args1,rest) ->
                                      let uu____14495 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14495 with
                                       | (xs2,c2) ->
                                           let uu____14508 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14508
                                             (fun uu____14532  ->
                                                match uu____14532 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14572 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14572 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14640 =
                                        let uu____14645 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14645 in
                                      FStar_All.pipe_right uu____14640
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14660 ->
                             let uu____14667 =
                               let uu____14668 =
                                 let uu____14673 =
                                   let uu____14674 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14675 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14676 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14674 uu____14675 uu____14676 in
                                 (uu____14673, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14668 in
                             FStar_Exn.raise uu____14667 in
                       let uu____14683 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14683
                         (fun uu____14738  ->
                            match uu____14738 with
                            | (xs1,c1) ->
                                let uu____14787 =
                                  let uu____14828 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____14828) in
                                FStar_Pervasives_Native.Some uu____14787)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____14949 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____14965 = project orig env wl1 i st in
                     match uu____14965 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____14979) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____14994 = imitate orig env wl1 st in
                  match uu____14994 with
                  | Failed uu____14999 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15030 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15030 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15053 = forced_lhs_pattern in
                    (match uu____15053 with
                     | (lhs_t,uu____15055,uu____15056,uu____15057) ->
                         ((let uu____15059 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel") in
                           if uu____15059
                           then
                             let uu____15060 = lhs1 in
                             match uu____15060 with
                             | (t0,uu____15062,uu____15063,uu____15064) ->
                                 let uu____15065 = forced_lhs_pattern in
                                 (match uu____15065 with
                                  | (t11,uu____15067,uu____15068,uu____15069)
                                      ->
                                      let uu____15070 =
                                        FStar_Syntax_Print.term_to_string t0 in
                                      let uu____15071 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15070 uu____15071)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t in
                           let uu____15079 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars in
                           if uu____15079
                           then
                             ((let uu____15081 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15081
                               then
                                 let uu____15082 =
                                   FStar_Syntax_Print.term_to_string rhs in
                                 let uu____15083 = names_to_string rhs_vars in
                                 let uu____15084 = names_to_string lhs_vars in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15082 uu____15083 uu____15084
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction () in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1 in
                               let uu____15088 =
                                 let uu____15089 =
                                   FStar_TypeChecker_Common.as_tprob orig in
                                 solve_t env uu____15089 wl2 in
                               match uu____15088 with
                               | Failed uu____15090 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15099 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15099
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt)))) in
              let check_head fvs1 t21 =
                let uu____15112 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15112 with
                | (hd1,uu____15128) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15149 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15162 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15163 -> true
                     | uu____15180 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15184 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15184
                         then true
                         else
                           ((let uu____15187 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15187
                             then
                               let uu____15188 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15188
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15208 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15208 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15221 =
                            let uu____15222 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15222 in
                          giveup_or_defer1 orig uu____15221
                        else
                          (let uu____15224 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15224
                           then
                             let uu____15225 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15225
                              then
                                let uu____15226 = subterms args_lhs in
                                imitate' orig env wl1 uu____15226
                              else
                                ((let uu____15231 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15231
                                  then
                                    let uu____15232 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15233 = names_to_string fvs1 in
                                    let uu____15234 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15232 uu____15233 uu____15234
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
                               (let uu____15238 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15238
                                then
                                  ((let uu____15240 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15240
                                    then
                                      let uu____15241 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15242 = names_to_string fvs1 in
                                      let uu____15243 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15241 uu____15242 uu____15243
                                    else ());
                                   (let uu____15245 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15245))
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
                     (let uu____15256 =
                        let uu____15257 = FStar_Syntax_Free.names t1 in
                        check_head uu____15257 t2 in
                      if uu____15256
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15268 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15268
                          then
                            let uu____15269 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15270 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15269 uu____15270
                          else ());
                         (let uu____15278 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15278))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15355 uu____15356 r =
               match (uu____15355, uu____15356) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15554 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15554
                   then
                     let uu____15555 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15555
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15579 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15579
                       then
                         let uu____15580 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15581 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15582 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15583 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15584 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15580 uu____15581 uu____15582 uu____15583
                           uu____15584
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15644 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15644 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15658 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15658 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15712 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15712 in
                                  let uu____15715 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15715 k3)
                           else
                             (let uu____15719 =
                                let uu____15720 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15721 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15722 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15720 uu____15721 uu____15722 in
                              failwith uu____15719) in
                       let uu____15723 =
                         let uu____15730 =
                           let uu____15743 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15743 in
                         match uu____15730 with
                         | (bs,k1') ->
                             let uu____15768 =
                               let uu____15781 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15781 in
                             (match uu____15768 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15809 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15809 in
                                  let uu____15818 =
                                    let uu____15823 =
                                      let uu____15824 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15824.FStar_Syntax_Syntax.n in
                                    let uu____15827 =
                                      let uu____15828 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15828.FStar_Syntax_Syntax.n in
                                    (uu____15823, uu____15827) in
                                  (match uu____15818 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15837,uu____15838) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____15841,FStar_Syntax_Syntax.Tm_type
                                      uu____15842) -> (k2'_ys, [sub_prob])
                                   | uu____15845 ->
                                       let uu____15850 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15850 with
                                        | (t,uu____15862) ->
                                            let uu____15863 = new_uvar r zs t in
                                            (match uu____15863 with
                                             | (k_zs,uu____15875) ->
                                                 let kprob =
                                                   let uu____15877 =
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
                                                          _0_64) uu____15877 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15723 with
                       | (k_u',sub_probs) ->
                           let uu____15894 =
                             let uu____15905 =
                               let uu____15906 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15906 in
                             let uu____15915 =
                               let uu____15918 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15918 in
                             let uu____15921 =
                               let uu____15924 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15924 in
                             (uu____15905, uu____15915, uu____15921) in
                           (match uu____15894 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15943 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15943 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15962 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15962
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15966 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15966 with
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
             let solve_one_pat uu____16019 uu____16020 =
               match (uu____16019, uu____16020) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16138 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16138
                     then
                       let uu____16139 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16140 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16139 uu____16140
                     else ());
                    (let uu____16142 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16142
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16161  ->
                              fun uu____16162  ->
                                match (uu____16161, uu____16162) with
                                | ((a,uu____16180),(t21,uu____16182)) ->
                                    let uu____16191 =
                                      let uu____16196 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16196
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16191
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16202 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16202 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16217 = occurs_check env wl (u1, k1) t21 in
                        match uu____16217 with
                        | (occurs_ok,uu____16225) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16233 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16233
                            then
                              let sol =
                                let uu____16235 =
                                  let uu____16244 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16244) in
                                TERM uu____16235 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16251 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16251
                               then
                                 let uu____16252 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16252 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16276,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16302 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16302
                                       then
                                         let uu____16303 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16303
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16310 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16312 = lhs in
             match uu____16312 with
             | (t1,u1,k1,args1) ->
                 let uu____16317 = rhs in
                 (match uu____16317 with
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
                       | uu____16357 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16367 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16367 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16385) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16392 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16392
                                    then
                                      let uu____16393 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16393
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16400 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16402 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16402
        then
          let uu____16403 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16403
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16407 = FStar_Util.physical_equality t1 t2 in
           if uu____16407
           then
             let uu____16408 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16408
           else
             ((let uu____16411 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16411
               then
                 let uu____16412 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16412
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16415,uu____16416) ->
                   let uu____16443 =
                     let uu___278_16444 = problem in
                     let uu____16445 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___278_16444.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16445;
                       FStar_TypeChecker_Common.relation =
                         (uu___278_16444.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___278_16444.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___278_16444.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___278_16444.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___278_16444.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___278_16444.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___278_16444.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___278_16444.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16443 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16446,uu____16447) ->
                   let uu____16454 =
                     let uu___278_16455 = problem in
                     let uu____16456 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___278_16455.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16456;
                       FStar_TypeChecker_Common.relation =
                         (uu___278_16455.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___278_16455.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___278_16455.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___278_16455.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___278_16455.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___278_16455.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___278_16455.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___278_16455.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16454 wl
               | (uu____16457,FStar_Syntax_Syntax.Tm_ascribed uu____16458) ->
                   let uu____16485 =
                     let uu___279_16486 = problem in
                     let uu____16487 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___279_16486.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___279_16486.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___279_16486.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16487;
                       FStar_TypeChecker_Common.element =
                         (uu___279_16486.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___279_16486.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___279_16486.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___279_16486.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___279_16486.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___279_16486.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16485 wl
               | (uu____16488,FStar_Syntax_Syntax.Tm_meta uu____16489) ->
                   let uu____16496 =
                     let uu___279_16497 = problem in
                     let uu____16498 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___279_16497.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___279_16497.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___279_16497.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16498;
                       FStar_TypeChecker_Common.element =
                         (uu___279_16497.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___279_16497.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___279_16497.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___279_16497.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___279_16497.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___279_16497.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16496 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16499,uu____16500) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16501,FStar_Syntax_Syntax.Tm_bvar uu____16502) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___242_16557 =
                     match uu___242_16557 with
                     | [] -> c
                     | bs ->
                         let uu____16579 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16579 in
                   let uu____16588 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16588 with
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
                                   let uu____16730 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16730
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16732 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16732))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___243_16808 =
                     match uu___243_16808 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16842 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16842 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16978 =
                                   let uu____16983 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16984 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16983
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16984 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16978))
               | (FStar_Syntax_Syntax.Tm_abs uu____16989,uu____16990) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17015 -> true
                     | uu____17032 -> false in
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
                       (let uu____17079 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___280_17087 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___280_17087.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___280_17087.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___280_17087.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___280_17087.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___280_17087.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___280_17087.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___280_17087.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___280_17087.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___280_17087.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___280_17087.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___280_17087.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___280_17087.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___280_17087.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___280_17087.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___280_17087.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___280_17087.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___280_17087.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___280_17087.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___280_17087.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___280_17087.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___280_17087.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___280_17087.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___280_17087.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___280_17087.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___280_17087.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___280_17087.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___280_17087.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___280_17087.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___280_17087.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___280_17087.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___280_17087.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17079 with
                        | (uu____17090,ty,uu____17092) ->
                            let uu____17093 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17093) in
                   let uu____17094 =
                     let uu____17111 = maybe_eta t1 in
                     let uu____17118 = maybe_eta t2 in
                     (uu____17111, uu____17118) in
                   (match uu____17094 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___281_17160 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___281_17160.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___281_17160.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___281_17160.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___281_17160.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___281_17160.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___281_17160.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___281_17160.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___281_17160.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17183 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17183
                        then
                          let uu____17184 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17184 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17199 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17199.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17199.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17199.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17199.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17199.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17199.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17199.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17199.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17223 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17223
                        then
                          let uu____17224 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17224 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17239 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17239.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17239.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17239.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17239.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17239.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17239.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17239.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17239.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17243 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17260,FStar_Syntax_Syntax.Tm_abs uu____17261) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17286 -> true
                     | uu____17303 -> false in
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
                       (let uu____17350 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___280_17358 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___280_17358.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___280_17358.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___280_17358.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___280_17358.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___280_17358.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___280_17358.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___280_17358.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___280_17358.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___280_17358.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___280_17358.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___280_17358.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___280_17358.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___280_17358.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___280_17358.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___280_17358.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___280_17358.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___280_17358.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___280_17358.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___280_17358.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___280_17358.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___280_17358.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___280_17358.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___280_17358.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___280_17358.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___280_17358.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___280_17358.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___280_17358.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___280_17358.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___280_17358.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___280_17358.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___280_17358.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17350 with
                        | (uu____17361,ty,uu____17363) ->
                            let uu____17364 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17364) in
                   let uu____17365 =
                     let uu____17382 = maybe_eta t1 in
                     let uu____17389 = maybe_eta t2 in
                     (uu____17382, uu____17389) in
                   (match uu____17365 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___281_17431 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___281_17431.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___281_17431.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___281_17431.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___281_17431.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___281_17431.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___281_17431.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___281_17431.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___281_17431.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17454 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17454
                        then
                          let uu____17455 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17455 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17470 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17470.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17470.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17470.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17470.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17470.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17470.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17470.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17470.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17494 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17494
                        then
                          let uu____17495 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17495 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___282_17510 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___282_17510.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___282_17510.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___282_17510.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___282_17510.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___282_17510.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___282_17510.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___282_17510.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___282_17510.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17514 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____17546 = FStar_Syntax_Free.uvars t1 in
                       FStar_Util.set_is_empty uu____17546) &&
                        (let uu____17558 = FStar_Syntax_Free.uvars t2 in
                         FStar_Util.set_is_empty uu____17558))
                       &&
                       (let uu____17573 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort in
                        match uu____17573 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___244_17583 =
                              match uu___244_17583 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____17584 -> true
                              | uu____17585 -> false in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____17586 -> false) in
                   let uu____17587 = as_refinement should_delta env wl t1 in
                   (match uu____17587 with
                    | (x11,phi1) ->
                        let uu____17594 =
                          as_refinement should_delta env wl t2 in
                        (match uu____17594 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____17602 =
                                 mk_problem (p_scope orig) orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17602 in
                             let x12 = FStar_Syntax_Syntax.freshen_bv x11 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x12)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi22 =
                               FStar_Syntax_Subst.subst subst1 phi21 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x12 in
                             let mk_imp1 imp phi12 phi23 =
                               let uu____17640 = imp phi12 phi23 in
                               FStar_All.pipe_right uu____17640
                                 (guard_on_element wl problem x12) in
                             let fallback uu____17644 =
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
                                 let uu____17650 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17650 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17659 =
                                   let uu____17664 =
                                     let uu____17665 =
                                       let uu____17672 =
                                         FStar_Syntax_Syntax.mk_binder x12 in
                                       [uu____17672] in
                                     FStar_List.append (p_scope orig)
                                       uu____17665 in
                                   mk_problem uu____17664 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17659 in
                               let uu____17681 =
                                 solve env1
                                   (let uu___283_17683 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___283_17683.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___283_17683.smt_ok);
                                      tcenv = (uu___283_17683.tcenv)
                                    }) in
                               (match uu____17681 with
                                | Failed uu____17690 -> fallback ()
                                | Success uu____17695 ->
                                    let guard =
                                      let uu____17699 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17704 =
                                        let uu____17705 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17705
                                          (guard_on_element wl problem x12) in
                                      FStar_Syntax_Util.mk_conj uu____17699
                                        uu____17704 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___284_17714 = wl1 in
                                      {
                                        attempting =
                                          (uu___284_17714.attempting);
                                        wl_deferred =
                                          (uu___284_17714.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___284_17714.defer_ok);
                                        smt_ok = (uu___284_17714.smt_ok);
                                        tcenv = (uu___284_17714.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17716,FStar_Syntax_Syntax.Tm_uvar uu____17717) ->
                   let uu____17750 = destruct_flex_t t1 in
                   let uu____17751 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17750 uu____17751
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17752;
                     FStar_Syntax_Syntax.pos = uu____17753;
                     FStar_Syntax_Syntax.vars = uu____17754;_},uu____17755),FStar_Syntax_Syntax.Tm_uvar
                  uu____17756) ->
                   let uu____17809 = destruct_flex_t t1 in
                   let uu____17810 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17809 uu____17810
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17811,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17812;
                     FStar_Syntax_Syntax.pos = uu____17813;
                     FStar_Syntax_Syntax.vars = uu____17814;_},uu____17815))
                   ->
                   let uu____17868 = destruct_flex_t t1 in
                   let uu____17869 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17868 uu____17869
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17870;
                     FStar_Syntax_Syntax.pos = uu____17871;
                     FStar_Syntax_Syntax.vars = uu____17872;_},uu____17873),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17874;
                     FStar_Syntax_Syntax.pos = uu____17875;
                     FStar_Syntax_Syntax.vars = uu____17876;_},uu____17877))
                   ->
                   let uu____17950 = destruct_flex_t t1 in
                   let uu____17951 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17950 uu____17951
               | (FStar_Syntax_Syntax.Tm_uvar uu____17952,uu____17953) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17970 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17970 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17977;
                     FStar_Syntax_Syntax.pos = uu____17978;
                     FStar_Syntax_Syntax.vars = uu____17979;_},uu____17980),uu____17981)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18018 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18018 t2 wl
               | (uu____18025,FStar_Syntax_Syntax.Tm_uvar uu____18026) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18043,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18044;
                     FStar_Syntax_Syntax.pos = uu____18045;
                     FStar_Syntax_Syntax.vars = uu____18046;_},uu____18047))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18084,FStar_Syntax_Syntax.Tm_type uu____18085) ->
                   solve_t' env
                     (let uu___285_18103 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18103.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18103.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18103.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18103.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18103.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18103.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18103.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18103.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18103.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18104;
                     FStar_Syntax_Syntax.pos = uu____18105;
                     FStar_Syntax_Syntax.vars = uu____18106;_},uu____18107),FStar_Syntax_Syntax.Tm_type
                  uu____18108) ->
                   solve_t' env
                     (let uu___285_18146 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18146.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18146.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18146.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18146.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18146.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18146.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18146.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18146.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18146.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18147,FStar_Syntax_Syntax.Tm_arrow uu____18148) ->
                   solve_t' env
                     (let uu___285_18178 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18178.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18178.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18178.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18178.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18178.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18178.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18178.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18178.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18178.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18179;
                     FStar_Syntax_Syntax.pos = uu____18180;
                     FStar_Syntax_Syntax.vars = uu____18181;_},uu____18182),FStar_Syntax_Syntax.Tm_arrow
                  uu____18183) ->
                   solve_t' env
                     (let uu___285_18233 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___285_18233.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___285_18233.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___285_18233.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___285_18233.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___285_18233.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___285_18233.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___285_18233.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___285_18233.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___285_18233.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18234,uu____18235) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18254 =
                        let uu____18255 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18255 in
                      if uu____18254
                      then
                        let uu____18256 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___286_18262 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___286_18262.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___286_18262.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___286_18262.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___286_18262.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___286_18262.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___286_18262.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___286_18262.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___286_18262.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___286_18262.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18263 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18256 uu____18263 t2
                          wl
                      else
                        (let uu____18271 = base_and_refinement env t2 in
                         match uu____18271 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18300 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___287_18306 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___287_18306.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___287_18306.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___287_18306.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___287_18306.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___287_18306.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___287_18306.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___287_18306.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___287_18306.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___287_18306.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18307 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18300
                                    uu____18307 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___288_18321 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___288_18321.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___288_18321.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18324 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18324 in
                                  let guard =
                                    let uu____18336 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18336
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18344;
                     FStar_Syntax_Syntax.pos = uu____18345;
                     FStar_Syntax_Syntax.vars = uu____18346;_},uu____18347),uu____18348)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18387 =
                        let uu____18388 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18388 in
                      if uu____18387
                      then
                        let uu____18389 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___286_18395 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___286_18395.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___286_18395.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___286_18395.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___286_18395.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___286_18395.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___286_18395.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___286_18395.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___286_18395.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___286_18395.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18396 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18389 uu____18396 t2
                          wl
                      else
                        (let uu____18404 = base_and_refinement env t2 in
                         match uu____18404 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18433 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___287_18439 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___287_18439.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___287_18439.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___287_18439.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___287_18439.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___287_18439.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___287_18439.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___287_18439.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___287_18439.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___287_18439.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18440 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18433
                                    uu____18440 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___288_18454 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___288_18454.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___288_18454.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18457 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18457 in
                                  let guard =
                                    let uu____18469 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18469
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18477,FStar_Syntax_Syntax.Tm_uvar uu____18478) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18496 = base_and_refinement env t1 in
                      match uu____18496 with
                      | (t_base,uu____18508) ->
                          solve_t env
                            (let uu___289_18522 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___289_18522.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___289_18522.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___289_18522.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___289_18522.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___289_18522.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___289_18522.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___289_18522.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___289_18522.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18523,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18524;
                     FStar_Syntax_Syntax.pos = uu____18525;
                     FStar_Syntax_Syntax.vars = uu____18526;_},uu____18527))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18565 = base_and_refinement env t1 in
                      match uu____18565 with
                      | (t_base,uu____18577) ->
                          solve_t env
                            (let uu___289_18591 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___289_18591.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___289_18591.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___289_18591.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___289_18591.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___289_18591.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___289_18591.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___289_18591.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___289_18591.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18592,uu____18593) ->
                   let t21 =
                     let uu____18603 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18603 in
                   solve_t env
                     (let uu___290_18627 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___290_18627.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___290_18627.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___290_18627.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___290_18627.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___290_18627.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___290_18627.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___290_18627.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___290_18627.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___290_18627.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18628,FStar_Syntax_Syntax.Tm_refine uu____18629) ->
                   let t11 =
                     let uu____18639 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18639 in
                   solve_t env
                     (let uu___291_18663 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___291_18663.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___291_18663.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___291_18663.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___291_18663.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___291_18663.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___291_18663.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___291_18663.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___291_18663.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___291_18663.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18666,uu____18667) ->
                   let head1 =
                     let uu____18693 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18693
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18737 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18737
                       FStar_Pervasives_Native.fst in
                   let uu____18778 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18778
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18793 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18793
                      then
                        let guard =
                          let uu____18805 =
                            let uu____18806 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18806 = FStar_Syntax_Util.Equal in
                          if uu____18805
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18810 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18810) in
                        let uu____18813 = solve_prob orig guard [] wl in
                        solve env uu____18813
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18816,uu____18817) ->
                   let head1 =
                     let uu____18827 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18827
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18871 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18871
                       FStar_Pervasives_Native.fst in
                   let uu____18912 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18912
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18927 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18927
                      then
                        let guard =
                          let uu____18939 =
                            let uu____18940 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18940 = FStar_Syntax_Util.Equal in
                          if uu____18939
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18944 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18944) in
                        let uu____18947 = solve_prob orig guard [] wl in
                        solve env uu____18947
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18950,uu____18951) ->
                   let head1 =
                     let uu____18955 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18955
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18999 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18999
                       FStar_Pervasives_Native.fst in
                   let uu____19040 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19040
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19055 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19055
                      then
                        let guard =
                          let uu____19067 =
                            let uu____19068 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19068 = FStar_Syntax_Util.Equal in
                          if uu____19067
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19072 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19072) in
                        let uu____19075 = solve_prob orig guard [] wl in
                        solve env uu____19075
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19078,uu____19079) ->
                   let head1 =
                     let uu____19083 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19083
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19127 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19127
                       FStar_Pervasives_Native.fst in
                   let uu____19168 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19168
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19183 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19183
                      then
                        let guard =
                          let uu____19195 =
                            let uu____19196 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19196 = FStar_Syntax_Util.Equal in
                          if uu____19195
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19200 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19200) in
                        let uu____19203 = solve_prob orig guard [] wl in
                        solve env uu____19203
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19206,uu____19207) ->
                   let head1 =
                     let uu____19211 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19211
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19255 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19255
                       FStar_Pervasives_Native.fst in
                   let uu____19296 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19296
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19311 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19311
                      then
                        let guard =
                          let uu____19323 =
                            let uu____19324 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19324 = FStar_Syntax_Util.Equal in
                          if uu____19323
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19328 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19328) in
                        let uu____19331 = solve_prob orig guard [] wl in
                        solve env uu____19331
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19334,uu____19335) ->
                   let head1 =
                     let uu____19353 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19353
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19397 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19397
                       FStar_Pervasives_Native.fst in
                   let uu____19438 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19438
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19453 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19453
                      then
                        let guard =
                          let uu____19465 =
                            let uu____19466 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19466 = FStar_Syntax_Util.Equal in
                          if uu____19465
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19470 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19470) in
                        let uu____19473 = solve_prob orig guard [] wl in
                        solve env uu____19473
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19476,FStar_Syntax_Syntax.Tm_match uu____19477) ->
                   let head1 =
                     let uu____19503 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19503
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19547 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19547
                       FStar_Pervasives_Native.fst in
                   let uu____19588 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19588
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19603 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19603
                      then
                        let guard =
                          let uu____19615 =
                            let uu____19616 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19616 = FStar_Syntax_Util.Equal in
                          if uu____19615
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19620 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19620) in
                        let uu____19623 = solve_prob orig guard [] wl in
                        solve env uu____19623
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19626,FStar_Syntax_Syntax.Tm_uinst uu____19627) ->
                   let head1 =
                     let uu____19637 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19637
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19681 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19681
                       FStar_Pervasives_Native.fst in
                   let uu____19722 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19722
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19737 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19737
                      then
                        let guard =
                          let uu____19749 =
                            let uu____19750 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19750 = FStar_Syntax_Util.Equal in
                          if uu____19749
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19754 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19754) in
                        let uu____19757 = solve_prob orig guard [] wl in
                        solve env uu____19757
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19760,FStar_Syntax_Syntax.Tm_name uu____19761) ->
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
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19882) in
                        let uu____19885 = solve_prob orig guard [] wl in
                        solve env uu____19885
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19888,FStar_Syntax_Syntax.Tm_constant uu____19889) ->
                   let head1 =
                     let uu____19893 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19893
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19937 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19937
                       FStar_Pervasives_Native.fst in
                   let uu____19978 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19978
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19993 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19993
                      then
                        let guard =
                          let uu____20005 =
                            let uu____20006 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20006 = FStar_Syntax_Util.Equal in
                          if uu____20005
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20010 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20010) in
                        let uu____20013 = solve_prob orig guard [] wl in
                        solve env uu____20013
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20016,FStar_Syntax_Syntax.Tm_fvar uu____20017) ->
                   let head1 =
                     let uu____20021 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20021
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20065 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20065
                       FStar_Pervasives_Native.fst in
                   let uu____20106 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20106
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20121 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20121
                      then
                        let guard =
                          let uu____20133 =
                            let uu____20134 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20134 = FStar_Syntax_Util.Equal in
                          if uu____20133
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20138 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20138) in
                        let uu____20141 = solve_prob orig guard [] wl in
                        solve env uu____20141
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20144,FStar_Syntax_Syntax.Tm_app uu____20145) ->
                   let head1 =
                     let uu____20163 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20163
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20207 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20207
                       FStar_Pervasives_Native.fst in
                   let uu____20248 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20248
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20263 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20263
                      then
                        let guard =
                          let uu____20275 =
                            let uu____20276 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20276 = FStar_Syntax_Util.Equal in
                          if uu____20275
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20280 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20280) in
                        let uu____20283 = solve_prob orig guard [] wl in
                        solve env uu____20283
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20286,uu____20287) ->
                   let uu____20300 =
                     let uu____20301 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20302 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20301
                       uu____20302 in
                   failwith uu____20300
               | (FStar_Syntax_Syntax.Tm_delayed uu____20303,uu____20304) ->
                   let uu____20329 =
                     let uu____20330 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20331 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20330
                       uu____20331 in
                   failwith uu____20329
               | (uu____20332,FStar_Syntax_Syntax.Tm_delayed uu____20333) ->
                   let uu____20358 =
                     let uu____20359 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20360 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20359
                       uu____20360 in
                   failwith uu____20358
               | (uu____20361,FStar_Syntax_Syntax.Tm_let uu____20362) ->
                   let uu____20375 =
                     let uu____20376 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20377 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20376
                       uu____20377 in
                   failwith uu____20375
               | uu____20378 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20414 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20414
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20416 =
               let uu____20417 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20418 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20417 uu____20418 in
             giveup env uu____20416 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20438  ->
                    fun uu____20439  ->
                      match (uu____20438, uu____20439) with
                      | ((a1,uu____20457),(a2,uu____20459)) ->
                          let uu____20468 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20468)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20478 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20478 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20502 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20509)::[] -> wp1
              | uu____20526 ->
                  let uu____20535 =
                    let uu____20536 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20536 in
                  failwith uu____20535 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20544 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____20544]
              | x -> x in
            let uu____20546 =
              let uu____20555 =
                let uu____20556 =
                  let uu____20557 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20557 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20556 in
              [uu____20555] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20546;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20558 = lift_c1 () in solve_eq uu____20558 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___245_20564  ->
                       match uu___245_20564 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20565 -> false)) in
             let uu____20566 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20600)::uu____20601,(wp2,uu____20603)::uu____20604)
                   -> (wp1, wp2)
               | uu____20661 ->
                   let uu____20682 =
                     let uu____20683 =
                       let uu____20688 =
                         let uu____20689 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20690 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20689 uu____20690 in
                       (uu____20688, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20683 in
                   FStar_Exn.raise uu____20682 in
             match uu____20566 with
             | (wpc1,wpc2) ->
                 let uu____20709 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20709
                 then
                   let uu____20712 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20712 wl
                 else
                   (let uu____20716 =
                      let uu____20723 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20723 in
                    match uu____20716 with
                    | (c2_decl,qualifiers) ->
                        let uu____20744 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20744
                        then
                          let c1_repr =
                            let uu____20748 =
                              let uu____20749 =
                                let uu____20750 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20750 in
                              let uu____20751 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20749 uu____20751 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20748 in
                          let c2_repr =
                            let uu____20753 =
                              let uu____20754 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20755 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20754 uu____20755 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20753 in
                          let prob =
                            let uu____20757 =
                              let uu____20762 =
                                let uu____20763 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20764 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20763
                                  uu____20764 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20762 in
                            FStar_TypeChecker_Common.TProb uu____20757 in
                          let wl1 =
                            let uu____20766 =
                              let uu____20769 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20769 in
                            solve_prob orig uu____20766 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20778 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20778
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____20781 =
                                     let uu____20784 =
                                       let uu____20785 =
                                         let uu____20800 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20801 =
                                           let uu____20804 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20805 =
                                             let uu____20808 =
                                               let uu____20809 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20809 in
                                             [uu____20808] in
                                           uu____20804 :: uu____20805 in
                                         (uu____20800, uu____20801) in
                                       FStar_Syntax_Syntax.Tm_app uu____20785 in
                                     FStar_Syntax_Syntax.mk uu____20784 in
                                   uu____20781 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____20818 =
                                    let uu____20821 =
                                      let uu____20822 =
                                        let uu____20837 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20838 =
                                          let uu____20841 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20842 =
                                            let uu____20845 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20846 =
                                              let uu____20849 =
                                                let uu____20850 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20850 in
                                              [uu____20849] in
                                            uu____20845 :: uu____20846 in
                                          uu____20841 :: uu____20842 in
                                        (uu____20837, uu____20838) in
                                      FStar_Syntax_Syntax.Tm_app uu____20822 in
                                    FStar_Syntax_Syntax.mk uu____20821 in
                                  uu____20818 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20857 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20857 in
                           let wl1 =
                             let uu____20867 =
                               let uu____20870 =
                                 let uu____20873 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20873 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20870 in
                             solve_prob orig uu____20867 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20886 = FStar_Util.physical_equality c1 c2 in
        if uu____20886
        then
          let uu____20887 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20887
        else
          ((let uu____20890 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20890
            then
              let uu____20891 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20892 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20891
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20892
            else ());
           (let uu____20894 =
              let uu____20899 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20900 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20899, uu____20900) in
            match uu____20894 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20904),FStar_Syntax_Syntax.Total
                    (t2,uu____20906)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20923 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20923 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20926,FStar_Syntax_Syntax.Total uu____20927) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20945),FStar_Syntax_Syntax.Total
                    (t2,uu____20947)) ->
                     let uu____20964 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20964 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20968),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20970)) ->
                     let uu____20987 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20987 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20991),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20993)) ->
                     let uu____21010 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21010 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21013,FStar_Syntax_Syntax.Comp uu____21014) ->
                     let uu____21023 =
                       let uu___292_21028 = problem in
                       let uu____21033 =
                         let uu____21034 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21034 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___292_21028.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21033;
                         FStar_TypeChecker_Common.relation =
                           (uu___292_21028.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___292_21028.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___292_21028.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___292_21028.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___292_21028.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___292_21028.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___292_21028.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___292_21028.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21023 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21035,FStar_Syntax_Syntax.Comp uu____21036) ->
                     let uu____21045 =
                       let uu___292_21050 = problem in
                       let uu____21055 =
                         let uu____21056 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21056 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___292_21050.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21055;
                         FStar_TypeChecker_Common.relation =
                           (uu___292_21050.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___292_21050.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___292_21050.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___292_21050.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___292_21050.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___292_21050.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___292_21050.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___292_21050.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21045 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21057,FStar_Syntax_Syntax.GTotal uu____21058) ->
                     let uu____21067 =
                       let uu___293_21072 = problem in
                       let uu____21077 =
                         let uu____21078 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21078 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___293_21072.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___293_21072.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___293_21072.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21077;
                         FStar_TypeChecker_Common.element =
                           (uu___293_21072.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___293_21072.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___293_21072.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___293_21072.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___293_21072.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___293_21072.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21067 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21079,FStar_Syntax_Syntax.Total uu____21080) ->
                     let uu____21089 =
                       let uu___293_21094 = problem in
                       let uu____21099 =
                         let uu____21100 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21100 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___293_21094.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___293_21094.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___293_21094.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21099;
                         FStar_TypeChecker_Common.element =
                           (uu___293_21094.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___293_21094.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___293_21094.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___293_21094.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___293_21094.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___293_21094.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21089 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21101,FStar_Syntax_Syntax.Comp uu____21102) ->
                     let uu____21103 =
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
                     if uu____21103
                     then
                       let uu____21104 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21104 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21110 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21120 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21121 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21120, uu____21121)) in
                          match uu____21110 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21128 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21128
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21130 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21130 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21133 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21135 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21135) in
                                if uu____21133
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
                                  (let uu____21138 =
                                     let uu____21139 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21140 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21139 uu____21140 in
                                   giveup env uu____21138 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21145 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21183  ->
              match uu____21183 with
              | (uu____21196,uu____21197,u,uu____21199,uu____21200,uu____21201)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21145 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21232 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21232 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21250 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21278  ->
                match uu____21278 with
                | (u1,u2) ->
                    let uu____21285 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21286 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21285 uu____21286)) in
      FStar_All.pipe_right uu____21250 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21303,[])) -> "{}"
      | uu____21328 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21345 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21345
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21348 =
              FStar_List.map
                (fun uu____21358  ->
                   match uu____21358 with
                   | (uu____21363,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21348 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21368 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21368 imps
let new_t_problem:
  'Auu____21376 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21376 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21376)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21410 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21410
                then
                  let uu____21411 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21412 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21411
                    (rel_to_string rel) uu____21412
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
            let uu____21436 =
              let uu____21439 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21439 in
            FStar_Syntax_Syntax.new_bv uu____21436 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21448 =
              let uu____21451 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21451 in
            let uu____21454 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21448 uu____21454 in
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
          let uu____21484 = FStar_Options.eager_inference () in
          if uu____21484
          then
            let uu___294_21485 = probs in
            {
              attempting = (uu___294_21485.attempting);
              wl_deferred = (uu___294_21485.wl_deferred);
              ctr = (uu___294_21485.ctr);
              defer_ok = false;
              smt_ok = (uu___294_21485.smt_ok);
              tcenv = (uu___294_21485.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21496 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21496
              then
                let uu____21497 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21497
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
          ((let uu____21511 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21511
            then
              let uu____21512 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21512
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____21516 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21516
             then
               let uu____21517 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21517
             else ());
            (let f2 =
               let uu____21520 =
                 let uu____21521 = FStar_Syntax_Util.unmeta f1 in
                 uu____21521.FStar_Syntax_Syntax.n in
               match uu____21520 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21525 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___295_21526 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___295_21526.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___295_21526.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___295_21526.FStar_TypeChecker_Env.implicits)
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
            let uu____21545 =
              let uu____21546 =
                let uu____21547 =
                  let uu____21548 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21548
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21547;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21546 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21545
let with_guard_no_simp:
  'Auu____21575 .
    'Auu____21575 ->
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
            let uu____21595 =
              let uu____21596 =
                let uu____21597 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21597
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21596;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21595
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
          (let uu____21635 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21635
           then
             let uu____21636 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21637 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21636
               uu____21637
           else ());
          (let prob =
             let uu____21640 =
               let uu____21645 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21645 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21640 in
           let g =
             let uu____21653 =
               let uu____21656 = singleton' env prob smt_ok in
               solve_and_commit env uu____21656
                 (fun uu____21658  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21653 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21676 = try_teq true env t1 t2 in
        match uu____21676 with
        | FStar_Pervasives_Native.None  ->
            let uu____21679 =
              let uu____21680 =
                let uu____21685 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21686 = FStar_TypeChecker_Env.get_range env in
                (uu____21685, uu____21686) in
              FStar_Errors.Error uu____21680 in
            FStar_Exn.raise uu____21679
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21689 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21689
              then
                let uu____21690 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21691 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21692 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21690
                  uu____21691 uu____21692
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
          let uu____21706 = FStar_TypeChecker_Env.get_range env in
          let uu____21707 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21706 uu____21707
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21720 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21720
         then
           let uu____21721 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21722 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21721
             uu____21722
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21727 =
             let uu____21732 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21732 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21727 in
         let uu____21737 =
           let uu____21740 = singleton env prob in
           solve_and_commit env uu____21740
             (fun uu____21742  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21737)
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
      fun uu____21771  ->
        match uu____21771 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21810 =
                 let uu____21811 =
                   let uu____21816 =
                     let uu____21817 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21818 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21817 uu____21818 in
                   let uu____21819 = FStar_TypeChecker_Env.get_range env in
                   (uu____21816, uu____21819) in
                 FStar_Errors.Error uu____21811 in
               FStar_Exn.raise uu____21810) in
            let equiv1 v1 v' =
              let uu____21827 =
                let uu____21832 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21833 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21832, uu____21833) in
              match uu____21827 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21852 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21882 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21882 with
                      | FStar_Syntax_Syntax.U_unif uu____21889 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21918  ->
                                    match uu____21918 with
                                    | (u,v') ->
                                        let uu____21927 = equiv1 v1 v' in
                                        if uu____21927
                                        then
                                          let uu____21930 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21930 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21946 -> [])) in
            let uu____21951 =
              let wl =
                let uu___296_21955 = empty_worklist env in
                {
                  attempting = (uu___296_21955.attempting);
                  wl_deferred = (uu___296_21955.wl_deferred);
                  ctr = (uu___296_21955.ctr);
                  defer_ok = false;
                  smt_ok = (uu___296_21955.smt_ok);
                  tcenv = (uu___296_21955.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21973  ->
                      match uu____21973 with
                      | (lb,v1) ->
                          let uu____21980 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21980 with
                           | USolved wl1 -> ()
                           | uu____21982 -> fail lb v1))) in
            let rec check_ineq uu____21990 =
              match uu____21990 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21999) -> true
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
                      uu____22022,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22024,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22035) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22042,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22050 -> false) in
            let uu____22055 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22070  ->
                      match uu____22070 with
                      | (u,v1) ->
                          let uu____22077 = check_ineq (u, v1) in
                          if uu____22077
                          then true
                          else
                            ((let uu____22080 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22080
                              then
                                let uu____22081 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22082 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22081
                                  uu____22082
                              else ());
                             false))) in
            if uu____22055
            then ()
            else
              ((let uu____22086 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22086
                then
                  ((let uu____22088 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22088);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22098 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22098))
                else ());
               (let uu____22108 =
                  let uu____22109 =
                    let uu____22114 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22114) in
                  FStar_Errors.Error uu____22109 in
                FStar_Exn.raise uu____22108))
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
      let fail uu____22162 =
        match uu____22162 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22176 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22176
       then
         let uu____22177 = wl_to_string wl in
         let uu____22178 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22177 uu____22178
       else ());
      (let g1 =
         let uu____22193 = solve_and_commit env wl fail in
         match uu____22193 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___297_22206 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___297_22206.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___297_22206.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___297_22206.FStar_TypeChecker_Env.implicits)
             }
         | uu____22211 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___298_22215 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___298_22215.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___298_22215.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___298_22215.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22237 = FStar_ST.op_Bang last_proof_ns in
    match uu____22237 with
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
            let uu___299_22427 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___299_22427.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___299_22427.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___299_22427.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22428 =
            let uu____22429 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22429 in
          if uu____22428
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22437 = FStar_TypeChecker_Env.get_range env in
                     let uu____22438 =
                       let uu____22439 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22439 in
                     FStar_Errors.diag uu____22437 uu____22438)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22443 = FStar_TypeChecker_Env.get_range env in
                      let uu____22444 =
                        let uu____22445 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22445 in
                      FStar_Errors.diag uu____22443 uu____22444)
                   else ();
                   (let uu____22447 = check_trivial vc1 in
                    match uu____22447 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22454 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22455 =
                                let uu____22456 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22456 in
                              FStar_Errors.diag uu____22454 uu____22455)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22461 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22462 =
                                let uu____22463 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22463 in
                              FStar_Errors.diag uu____22461 uu____22462)
                           else ();
                           (let vcs =
                              let uu____22474 = FStar_Options.use_tactics () in
                              if uu____22474
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22493  ->
                                     (let uu____22495 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22495);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22497 =
                                   let uu____22504 = FStar_Options.peek () in
                                   (env, vc2, uu____22504) in
                                 [uu____22497]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22538  ->
                                    match uu____22538 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22549 = check_trivial goal1 in
                                        (match uu____22549 with
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
                                                (let uu____22557 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22558 =
                                                   let uu____22559 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22560 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22559 uu____22560 in
                                                 FStar_Errors.diag
                                                   uu____22557 uu____22558)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22563 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22564 =
                                                   let uu____22565 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22565 in
                                                 FStar_Errors.diag
                                                   uu____22563 uu____22564)
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
      let uu____22575 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22575 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22581 =
            let uu____22582 =
              let uu____22587 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22587) in
            FStar_Errors.Error uu____22582 in
          FStar_Exn.raise uu____22581
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22594 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22594 with
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
          let uu____22613 = FStar_Syntax_Unionfind.find u in
          match uu____22613 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22616 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22634 = acc in
          match uu____22634 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22720 = hd1 in
                   (match uu____22720 with
                    | (uu____22733,env,u,tm,k,r) ->
                        let uu____22739 = unresolved u in
                        if uu____22739
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22770 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22770
                            then
                              let uu____22771 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22772 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22773 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22771 uu____22772 uu____22773
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___300_22776 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___300_22776.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___300_22776.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___300_22776.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___300_22776.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___300_22776.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___300_22776.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___300_22776.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___300_22776.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___300_22776.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___300_22776.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___300_22776.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___300_22776.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___300_22776.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___300_22776.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___300_22776.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___300_22776.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___300_22776.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___300_22776.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___300_22776.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___300_22776.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___300_22776.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___300_22776.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___300_22776.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___300_22776.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___300_22776.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___300_22776.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___300_22776.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___300_22776.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___300_22776.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___300_22776.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___300_22776.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___300_22776.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___300_22776.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____22779 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___301_22787 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___301_22787.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___301_22787.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___301_22787.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___301_22787.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___301_22787.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___301_22787.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___301_22787.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___301_22787.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___301_22787.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___301_22787.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___301_22787.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___301_22787.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___301_22787.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___301_22787.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___301_22787.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___301_22787.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___301_22787.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___301_22787.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___301_22787.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___301_22787.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___301_22787.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___301_22787.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___301_22787.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___301_22787.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___301_22787.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___301_22787.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___301_22787.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___301_22787.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___301_22787.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___301_22787.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___301_22787.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___301_22787.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.dep_graph =
                                         (uu___301_22787.FStar_TypeChecker_Env.dep_graph)
                                     }) tm1 in
                                match uu____22779 with
                                | (uu____22788,uu____22789,g1) -> g1
                              else
                                (let uu____22792 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___302_22800 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___302_22800.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___302_22800.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___302_22800.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___302_22800.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___302_22800.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___302_22800.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___302_22800.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___302_22800.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___302_22800.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___302_22800.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___302_22800.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___302_22800.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___302_22800.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___302_22800.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___302_22800.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___302_22800.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___302_22800.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___302_22800.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___302_22800.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___302_22800.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___302_22800.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___302_22800.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___302_22800.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___302_22800.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___302_22800.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___302_22800.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___302_22800.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___302_22800.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___302_22800.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___302_22800.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___302_22800.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___302_22800.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___302_22800.FStar_TypeChecker_Env.dep_graph)
                                      }) tm1 in
                                 match uu____22792 with
                                 | (uu____22801,uu____22802,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___303_22805 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___303_22805.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___303_22805.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___303_22805.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____22808 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____22814  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____22808 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___304_22842 = g in
        let uu____22843 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___304_22842.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___304_22842.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___304_22842.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____22843
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
        let uu____22897 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22897 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22910 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22910
      | (reason,uu____22912,uu____22913,e,t,r)::uu____22917 ->
          let uu____22944 =
            let uu____22945 =
              let uu____22950 =
                let uu____22951 = FStar_Syntax_Print.term_to_string t in
                let uu____22952 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22951 uu____22952 in
              (uu____22950, r) in
            FStar_Errors.Error uu____22945 in
          FStar_Exn.raise uu____22944
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___305_22959 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___305_22959.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___305_22959.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___305_22959.FStar_TypeChecker_Env.implicits)
      }
let discharge_guard_nosmt:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun env  ->
    fun g  ->
      let uu____22982 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22982 with
      | FStar_Pervasives_Native.Some uu____22987 -> true
      | FStar_Pervasives_Native.None  -> false
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22997 = try_teq false env t1 t2 in
        match uu____22997 with
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
        (let uu____23017 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23017
         then
           let uu____23018 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23019 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23018
             uu____23019
         else ());
        (let uu____23021 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23021 with
         | (prob,x) ->
             let g =
               let uu____23037 =
                 let uu____23040 = singleton' env prob true in
                 solve_and_commit env uu____23040
                   (fun uu____23042  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23037 in
             ((let uu____23052 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____23052
               then
                 let uu____23053 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____23054 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____23055 =
                   let uu____23056 = FStar_Util.must g in
                   guard_to_string env uu____23056 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23053 uu____23054 uu____23055
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
        let uu____23084 = check_subtyping env t1 t2 in
        match uu____23084 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23103 =
              let uu____23104 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____23104 g in
            FStar_Pervasives_Native.Some uu____23103
let get_subtyping_prop:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23116 = check_subtyping env t1 t2 in
        match uu____23116 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23135 =
              let uu____23136 =
                let uu____23137 = FStar_Syntax_Syntax.mk_binder x in
                [uu____23137] in
              close_guard env uu____23136 g in
            FStar_Pervasives_Native.Some uu____23135
let subtype_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23148 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23148
         then
           let uu____23149 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23150 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23149
             uu____23150
         else ());
        (let uu____23152 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23152 with
         | (prob,x) ->
             let g =
               let uu____23162 =
                 let uu____23165 = singleton' env prob false in
                 solve_and_commit env uu____23165
                   (fun uu____23167  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23162 in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23178 =
                      let uu____23179 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____23179] in
                    close_guard env uu____23178 g1 in
                  discharge_guard_nosmt env g2))