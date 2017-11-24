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
          let uu___244_91 = g in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___244_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___244_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___244_91.FStar_TypeChecker_Env.implicits)
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
          let uu___245_175 = g in
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
              (uu___245_175.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___245_175.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___245_175.FStar_TypeChecker_Env.implicits)
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
          let uu___246_218 = g in
          let uu____219 =
            let uu____220 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____220 in
          {
            FStar_TypeChecker_Env.guard_f = uu____219;
            FStar_TypeChecker_Env.deferred =
              (uu___246_218.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___246_218.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___246_218.FStar_TypeChecker_Env.implicits)
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
            let uu___247_344 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___247_344.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___247_344.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___247_344.FStar_TypeChecker_Env.implicits)
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
            let uu___248_376 = g in
            let uu____377 =
              let uu____378 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____378 in
            {
              FStar_TypeChecker_Env.guard_f = uu____377;
              FStar_TypeChecker_Env.deferred =
                (uu___248_376.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___248_376.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___248_376.FStar_TypeChecker_Env.implicits)
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
  fun uu___216_812  ->
    match uu___216_812 with
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
    fun uu___217_909  ->
      match uu___217_909 with
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
    fun uu___218_943  ->
      match uu___218_943 with
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
        let uu___249_1063 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___249_1063.wl_deferred);
          ctr = (uu___249_1063.ctr);
          defer_ok = (uu___249_1063.defer_ok);
          smt_ok;
          tcenv = (uu___249_1063.tcenv)
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
      let uu___250_1094 = empty_worklist env in
      let uu____1095 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1095;
        wl_deferred = (uu___250_1094.wl_deferred);
        ctr = (uu___250_1094.ctr);
        defer_ok = false;
        smt_ok = (uu___250_1094.smt_ok);
        tcenv = (uu___250_1094.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___251_1109 = wl in
        {
          attempting = (uu___251_1109.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___251_1109.ctr);
          defer_ok = (uu___251_1109.defer_ok);
          smt_ok = (uu___251_1109.smt_ok);
          tcenv = (uu___251_1109.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___252_1126 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___252_1126.wl_deferred);
        ctr = (uu___252_1126.ctr);
        defer_ok = (uu___252_1126.defer_ok);
        smt_ok = (uu___252_1126.smt_ok);
        tcenv = (uu___252_1126.tcenv)
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
  fun uu___219_1142  ->
    match uu___219_1142 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1146 'Auu____1147 .
    ('Auu____1147,'Auu____1146) FStar_TypeChecker_Common.problem ->
      ('Auu____1147,'Auu____1146) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___253_1164 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___253_1164.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___253_1164.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___253_1164.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___253_1164.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___253_1164.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___253_1164.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___253_1164.FStar_TypeChecker_Common.rank)
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
  fun uu___220_1193  ->
    match uu___220_1193 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___221_1217  ->
      match uu___221_1217 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___222_1220  ->
    match uu___222_1220 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___223_1233  ->
    match uu___223_1233 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___224_1248  ->
    match uu___224_1248 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___225_1263  ->
    match uu___225_1263 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___226_1280  ->
    match uu___226_1280 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___227_1297  ->
    match uu___227_1297 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___228_1310  ->
    match uu___228_1310 with
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
         (fun uu___229_1680  ->
            match uu___229_1680 with
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
        (fun uu___230_1714  ->
           match uu___230_1714 with
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
        (fun uu___231_1749  ->
           match uu___231_1749 with
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
                    let uu___254_1841 = x in
                    let uu____1842 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___254_1841.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___254_1841.FStar_Syntax_Syntax.index);
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
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                              FStar_Syntax_Syntax.term'
                                                                FStar_Syntax_Syntax.syntax)
                                                              FStar_Pervasives_Native.tuple2
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = base_and_refinement_maybe_delta false
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
    let uu____2706 = FStar_Syntax_Syntax.null_bv t in
    (uu____2706, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2711 .
    FStar_TypeChecker_Env.env ->
      'Auu____2711 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2728 = base_and_refinement_maybe_delta true env t in
        match uu____2728 with
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
  fun uu____2807  ->
    match uu____2807 with
    | (t_base,refopt) ->
        let uu____2834 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2834 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2866 =
      let uu____2869 =
        let uu____2872 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2895  ->
                  match uu____2895 with | (uu____2902,uu____2903,x) -> x)) in
        FStar_List.append wl.attempting uu____2872 in
      FStar_List.map (wl_prob_to_string wl) uu____2869 in
    FStar_All.pipe_right uu____2866 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2916 =
          let uu____2929 =
            let uu____2930 = FStar_Syntax_Subst.compress k in
            uu____2930.FStar_Syntax_Syntax.n in
          match uu____2929 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2983 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2983)
              else
                (let uu____2997 = FStar_Syntax_Util.abs_formals t in
                 match uu____2997 with
                 | (ys',t1,uu____3020) ->
                     let uu____3025 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3025))
          | uu____3066 ->
              let uu____3067 =
                let uu____3078 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3078) in
              ((ys, t), uu____3067) in
        match uu____2916 with
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
                 let uu____3127 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3127 c in
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
            let uu____3155 = p_guard prob in
            match uu____3155 with
            | (uu____3160,uv) ->
                ((let uu____3163 =
                    let uu____3164 = FStar_Syntax_Subst.compress uv in
                    uu____3164.FStar_Syntax_Syntax.n in
                  match uu____3163 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3196 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3196
                        then
                          let uu____3197 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3198 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3199 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3197
                            uu____3198 uu____3199
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3201 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___255_3204 = wl in
                  {
                    attempting = (uu___255_3204.attempting);
                    wl_deferred = (uu___255_3204.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___255_3204.defer_ok);
                    smt_ok = (uu___255_3204.smt_ok);
                    tcenv = (uu___255_3204.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3219 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3219
         then
           let uu____3220 = FStar_Util.string_of_int pid in
           let uu____3221 =
             let uu____3222 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3222 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3220 uu____3221
         else ());
        commit sol;
        (let uu___256_3229 = wl in
         {
           attempting = (uu___256_3229.attempting);
           wl_deferred = (uu___256_3229.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___256_3229.defer_ok);
           smt_ok = (uu___256_3229.smt_ok);
           tcenv = (uu___256_3229.tcenv)
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
            | (uu____3267,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3279 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3279 in
          (let uu____3285 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3285
           then
             let uu____3286 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3287 =
               let uu____3288 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3288 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3286 uu____3287
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
        let uu____3320 =
          let uu____3327 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3327 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3320
          (FStar_Util.for_some
             (fun uu____3363  ->
                match uu____3363 with
                | (uv,uu____3369) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3376 'Auu____3377 .
    'Auu____3377 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3376)
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
            let uu____3409 = occurs wl uk t in Prims.op_Negation uu____3409 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3416 =
                 let uu____3417 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3418 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3417 uu____3418 in
               FStar_Pervasives_Native.Some uu____3416) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3428 'Auu____3429 .
    'Auu____3429 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3428)
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
            let uu____3483 = occurs_check env wl uk t in
            match uu____3483 with
            | (occurs_ok,msg) ->
                let uu____3514 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3514, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3537 'Auu____3538 .
    (FStar_Syntax_Syntax.bv,'Auu____3538) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3537) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3537) FStar_Pervasives_Native.tuple2
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
      let uu____3622 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3676  ->
                fun uu____3677  ->
                  match (uu____3676, uu____3677) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3758 =
                        let uu____3759 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3759 in
                      if uu____3758
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3784 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3784
                         then
                           let uu____3797 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3797)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3622 with | (isect,uu____3838) -> FStar_List.rev isect
let binders_eq:
  'Auu____3863 'Auu____3864 .
    (FStar_Syntax_Syntax.bv,'Auu____3864) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3863) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3919  ->
              fun uu____3920  ->
                match (uu____3919, uu____3920) with
                | ((a,uu____3938),(b,uu____3940)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3954 'Auu____3955 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3955) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3954)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3954)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4006 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4020  ->
                      match uu____4020 with
                      | (b,uu____4026) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4006
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4042 -> FStar_Pervasives_Native.None
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
            let uu____4115 = pat_var_opt env seen hd1 in
            (match uu____4115 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4129 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4129
                   then
                     let uu____4130 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4130
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4148 =
      let uu____4149 = FStar_Syntax_Subst.compress t in
      uu____4149.FStar_Syntax_Syntax.n in
    match uu____4148 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4152 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4169;
           FStar_Syntax_Syntax.pos = uu____4170;
           FStar_Syntax_Syntax.vars = uu____4171;_},uu____4172)
        -> true
    | uu____4209 -> false
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
           FStar_Syntax_Syntax.pos = uu____4333;
           FStar_Syntax_Syntax.vars = uu____4334;_},args)
        -> (t, uv, k, args)
    | uu____4402 -> failwith "Not a flex-uvar"
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
      let uu____4479 = destruct_flex_t t in
      match uu____4479 with
      | (t1,uv,k,args) ->
          let uu____4594 = pat_vars env [] args in
          (match uu____4594 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4692 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4773 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4808 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4812 -> false
let head_match: match_result -> match_result =
  fun uu___232_4815  ->
    match uu___232_4815 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4830 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4839 ->
          let uu____4840 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4840 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4851 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4870 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4879 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4906 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4907 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4908 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4925 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4938 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4962) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4968,uu____4969) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5011) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5032;
             FStar_Syntax_Syntax.index = uu____5033;
             FStar_Syntax_Syntax.sort = t2;_},uu____5035)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5042 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5043 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5044 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5057 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5075 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5075
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
            let uu____5096 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5096
            then FullMatch
            else
              (let uu____5098 =
                 let uu____5107 =
                   let uu____5110 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5110 in
                 let uu____5111 =
                   let uu____5114 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5114 in
                 (uu____5107, uu____5111) in
               MisMatch uu____5098)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5120),FStar_Syntax_Syntax.Tm_uinst (g,uu____5122)) ->
            let uu____5131 = head_matches env f g in
            FStar_All.pipe_right uu____5131 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5134 = FStar_Const.eq_const c d in
            if uu____5134
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5141),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5143)) ->
            let uu____5192 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5192
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5199),FStar_Syntax_Syntax.Tm_refine (y,uu____5201)) ->
            let uu____5210 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5210 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5212),uu____5213) ->
            let uu____5218 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5218 head_match
        | (uu____5219,FStar_Syntax_Syntax.Tm_refine (x,uu____5221)) ->
            let uu____5226 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5226 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5227,FStar_Syntax_Syntax.Tm_type
           uu____5228) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5229,FStar_Syntax_Syntax.Tm_arrow uu____5230) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5256),FStar_Syntax_Syntax.Tm_app (head',uu____5258))
            ->
            let uu____5299 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5299 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5301),uu____5302) ->
            let uu____5323 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5323 head_match
        | (uu____5324,FStar_Syntax_Syntax.Tm_app (head1,uu____5326)) ->
            let uu____5347 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5347 head_match
        | uu____5348 ->
            let uu____5353 =
              let uu____5362 = delta_depth_of_term env t11 in
              let uu____5365 = delta_depth_of_term env t21 in
              (uu____5362, uu____5365) in
            MisMatch uu____5353
let head_matches_delta:
  'Auu____5377 .
    FStar_TypeChecker_Env.env ->
      'Auu____5377 ->
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
            let uu____5410 = FStar_Syntax_Util.head_and_args t in
            match uu____5410 with
            | (head1,uu____5428) ->
                let uu____5449 =
                  let uu____5450 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5450.FStar_Syntax_Syntax.n in
                (match uu____5449 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5456 =
                       let uu____5457 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5457 FStar_Option.isSome in
                     if uu____5456
                     then
                       let uu____5476 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5476
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5480 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5583)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5601 =
                     let uu____5610 = maybe_inline t11 in
                     let uu____5613 = maybe_inline t21 in
                     (uu____5610, uu____5613) in
                   match uu____5601 with
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
                (uu____5650,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5668 =
                     let uu____5677 = maybe_inline t11 in
                     let uu____5680 = maybe_inline t21 in
                     (uu____5677, uu____5680) in
                   match uu____5668 with
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
                let uu____5723 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5723 with
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
                let uu____5746 =
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
                (match uu____5746 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5770 -> fail r
            | uu____5779 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5812 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____5848 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___233_5860  ->
    match uu___233_5860 with
    | T (t,uu____5862) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5878 = FStar_Syntax_Util.type_u () in
      match uu____5878 with
      | (t,uu____5884) ->
          let uu____5885 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____5885
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5896 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____5896 FStar_Pervasives_Native.fst
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
        let uu____5960 = head_matches env t1 t' in
        match uu____5960 with
        | MisMatch uu____5961 -> false
        | uu____5970 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6066,imp),T (t2,uu____6069)) -> (t2, imp)
                     | uu____6088 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6155  ->
                    match uu____6155 with
                    | (t2,uu____6169) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6212 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6212 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6287))::tcs2) ->
                       aux
                         (((let uu___257_6322 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___257_6322.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___257_6322.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6340 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___234_6393 =
                 match uu___234_6393 with
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
               let uu____6510 = decompose1 [] bs1 in
               (rebuild, matches, uu____6510))
      | uu____6559 ->
          let rebuild uu___235_6565 =
            match uu___235_6565 with
            | [] -> t1
            | uu____6568 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___236_6599  ->
    match uu___236_6599 with
    | T (t,uu____6601) -> t
    | uu____6610 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___237_6613  ->
    match uu___237_6613 with
    | T (t,uu____6615) -> FStar_Syntax_Syntax.as_arg t
    | uu____6624 -> failwith "Impossible"
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
              | (uu____6730,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6755 = new_uvar r scope1 k in
                  (match uu____6755 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6773 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6790 =
                         let uu____6791 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6791 in
                       ((T (gi_xs, mk_kind)), uu____6790))
              | (uu____6804,uu____6805,C uu____6806) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____6953 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
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
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7029 in
                             (uu____7028, [prob])
                         | uu____7032 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7047;
                         FStar_Syntax_Syntax.vars = uu____7048;_})
                        ->
                        let uu____7071 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7071 with
                         | (T (gi_xs,uu____7095),prob) ->
                             let uu____7105 =
                               let uu____7106 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7106 in
                             (uu____7105, [prob])
                         | uu____7109 -> failwith "impossible")
                    | (uu____7120,uu____7121,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7123;
                         FStar_Syntax_Syntax.vars = uu____7124;_})
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
                        let uu____7255 =
                          let uu____7264 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7264 FStar_List.unzip in
                        (match uu____7255 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7318 =
                                 let uu____7319 =
                                   let uu____7322 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7322 un_T in
                                 let uu____7323 =
                                   let uu____7332 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7332
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7319;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7323;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7318 in
                             ((C gi_xs), sub_probs))
                    | uu____7341 ->
                        let uu____7354 = sub_prob scope1 args q in
                        (match uu____7354 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____6953 with
                   | (tc,probs) ->
                       let uu____7385 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7448,uu____7449),T
                            (t,uu____7451)) ->
                             let b1 =
                               ((let uu___258_7488 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___258_7488.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___258_7488.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7489 =
                               let uu____7496 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7496 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7489)
                         | uu____7531 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7385 with
                        | (bopt,scope2,args1) ->
                            let uu____7615 = aux scope2 args1 qs2 in
                            (match uu____7615 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7652 =
                                         let uu____7655 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7655 in
                                       FStar_Syntax_Util.mk_conj_l uu____7652
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7678 =
                                         let uu____7681 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7682 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7681 :: uu____7682 in
                                       FStar_Syntax_Util.mk_conj_l uu____7678 in
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
  'Auu____7750 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7750)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7750)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___259_7771 = p in
      let uu____7776 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7777 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___259_7771.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7776;
        FStar_TypeChecker_Common.relation =
          (uu___259_7771.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7777;
        FStar_TypeChecker_Common.element =
          (uu___259_7771.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___259_7771.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___259_7771.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___259_7771.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___259_7771.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___259_7771.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7789 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7789
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7798 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____7818 = compress_prob wl pr in
        FStar_All.pipe_right uu____7818 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7828 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____7828 with
           | (lh,uu____7848) ->
               let uu____7869 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____7869 with
                | (rh,uu____7889) ->
                    let uu____7910 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7927,FStar_Syntax_Syntax.Tm_uvar uu____7928)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7965,uu____7966)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____7987,FStar_Syntax_Syntax.Tm_uvar uu____7988)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8009,uu____8010)
                          ->
                          let uu____8027 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8027 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8090 ->
                                    let rank =
                                      let uu____8100 = is_top_level_prob prob in
                                      if uu____8100
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8102 =
                                      let uu___260_8107 = tp in
                                      let uu____8112 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___260_8107.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___260_8107.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___260_8107.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8112;
                                        FStar_TypeChecker_Common.element =
                                          (uu___260_8107.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___260_8107.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___260_8107.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___260_8107.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___260_8107.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___260_8107.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8102)))
                      | (uu____8127,FStar_Syntax_Syntax.Tm_uvar uu____8128)
                          ->
                          let uu____8145 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8145 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8208 ->
                                    let uu____8217 =
                                      let uu___261_8224 = tp in
                                      let uu____8229 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___261_8224.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8229;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___261_8224.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___261_8224.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___261_8224.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___261_8224.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___261_8224.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___261_8224.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___261_8224.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___261_8224.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8217)))
                      | (uu____8250,uu____8251) -> (rigid_rigid, tp) in
                    (match uu____7910 with
                     | (rank,tp1) ->
                         let uu____8270 =
                           FStar_All.pipe_right
                             (let uu___262_8276 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___262_8276.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___262_8276.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___262_8276.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___262_8276.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___262_8276.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___262_8276.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___262_8276.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___262_8276.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___262_8276.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8270))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8286 =
            FStar_All.pipe_right
              (let uu___263_8292 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___263_8292.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___263_8292.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___263_8292.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___263_8292.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___263_8292.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___263_8292.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___263_8292.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___263_8292.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___263_8292.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8286)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8347 probs =
      match uu____8347 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8400 = rank wl hd1 in
               (match uu____8400 with
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
    match projectee with | UDeferred _0 -> true | uu____8507 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8519 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8531 -> false
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
                        let uu____8571 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8571 with
                        | (k,uu____8577) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8587 -> false)))
            | uu____8588 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8639 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8639 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8642 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8652 =
                     let uu____8653 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8654 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8653
                       uu____8654 in
                   UFailed uu____8652)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8674 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8674 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8696 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8696 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8699 ->
                let uu____8704 =
                  let uu____8705 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8706 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8705
                    uu____8706 msg in
                UFailed uu____8704 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8707,uu____8708) ->
              let uu____8709 =
                let uu____8710 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8711 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8710 uu____8711 in
              failwith uu____8709
          | (FStar_Syntax_Syntax.U_unknown ,uu____8712) ->
              let uu____8713 =
                let uu____8714 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8715 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8714 uu____8715 in
              failwith uu____8713
          | (uu____8716,FStar_Syntax_Syntax.U_bvar uu____8717) ->
              let uu____8718 =
                let uu____8719 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8720 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8719 uu____8720 in
              failwith uu____8718
          | (uu____8721,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8722 =
                let uu____8723 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8724 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8723 uu____8724 in
              failwith uu____8722
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8748 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8748
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8770 = occurs_univ v1 u3 in
              if uu____8770
              then
                let uu____8771 =
                  let uu____8772 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8773 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8772 uu____8773 in
                try_umax_components u11 u21 uu____8771
              else
                (let uu____8775 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8775)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8795 = occurs_univ v1 u3 in
              if uu____8795
              then
                let uu____8796 =
                  let uu____8797 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8798 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8797 uu____8798 in
                try_umax_components u11 u21 uu____8796
              else
                (let uu____8800 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8800)
          | (FStar_Syntax_Syntax.U_max uu____8809,uu____8810) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8816 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8816
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8818,FStar_Syntax_Syntax.U_max uu____8819) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8825 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8825
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8827,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8828,FStar_Syntax_Syntax.U_name
             uu____8829) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8830) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8831) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8832,FStar_Syntax_Syntax.U_succ
             uu____8833) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8834,FStar_Syntax_Syntax.U_zero
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
      let uu____8920 = bc1 in
      match uu____8920 with
      | (bs1,mk_cod1) ->
          let uu____8961 = bc2 in
          (match uu____8961 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9031 = FStar_Util.first_N n1 bs in
                 match uu____9031 with
                 | (bs3,rest) ->
                     let uu____9056 = mk_cod rest in (bs3, uu____9056) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9085 =
                   let uu____9092 = mk_cod1 [] in (bs1, uu____9092) in
                 let uu____9095 =
                   let uu____9102 = mk_cod2 [] in (bs2, uu____9102) in
                 (uu____9085, uu____9095)
               else
                 if l1 > l2
                 then
                   (let uu____9144 = curry l2 bs1 mk_cod1 in
                    let uu____9157 =
                      let uu____9164 = mk_cod2 [] in (bs2, uu____9164) in
                    (uu____9144, uu____9157))
                 else
                   (let uu____9180 =
                      let uu____9187 = mk_cod1 [] in (bs1, uu____9187) in
                    let uu____9190 = curry l1 bs2 mk_cod2 in
                    (uu____9180, uu____9190)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9311 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9311
       then
         let uu____9312 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9312
       else ());
      (let uu____9314 = next_prob probs in
       match uu____9314 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___264_9335 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___264_9335.wl_deferred);
               ctr = (uu___264_9335.ctr);
               defer_ok = (uu___264_9335.defer_ok);
               smt_ok = (uu___264_9335.smt_ok);
               tcenv = (uu___264_9335.tcenv)
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
                  let uu____9346 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9346 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9351 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9351 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9356,uu____9357) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9374 ->
                let uu____9383 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9442  ->
                          match uu____9442 with
                          | (c,uu____9450,uu____9451) -> c < probs.ctr)) in
                (match uu____9383 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9492 =
                            FStar_List.map
                              (fun uu____9507  ->
                                 match uu____9507 with
                                 | (uu____9518,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9492
                      | uu____9521 ->
                          let uu____9530 =
                            let uu___265_9531 = probs in
                            let uu____9532 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9553  ->
                                      match uu____9553 with
                                      | (uu____9560,uu____9561,y) -> y)) in
                            {
                              attempting = uu____9532;
                              wl_deferred = rest;
                              ctr = (uu___265_9531.ctr);
                              defer_ok = (uu___265_9531.defer_ok);
                              smt_ok = (uu___265_9531.smt_ok);
                              tcenv = (uu___265_9531.tcenv)
                            } in
                          solve env uu____9530))))
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
            let uu____9568 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9568 with
            | USolved wl1 ->
                let uu____9570 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9570
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
                  let uu____9616 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9616 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9619 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9631;
                  FStar_Syntax_Syntax.vars = uu____9632;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9635;
                  FStar_Syntax_Syntax.vars = uu____9636;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9650,uu____9651) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9658,FStar_Syntax_Syntax.Tm_uinst uu____9659) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9666 -> USolved wl
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
            ((let uu____9676 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9676
              then
                let uu____9677 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9677 msg
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
        (let uu____9686 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9686
         then
           let uu____9687 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9687
         else ());
        (let uu____9689 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9689 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9751 = head_matches_delta env () t1 t2 in
               match uu____9751 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9792 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____9841 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9856 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____9857 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____9856, uu____9857)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9862 = FStar_Syntax_Subst.compress t1 in
                              let uu____9863 = FStar_Syntax_Subst.compress t2 in
                              (uu____9862, uu____9863) in
                        (match uu____9841 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____9889 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____9889 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____9920 =
                                    let uu____9929 =
                                      let uu____9932 =
                                        let uu____9935 =
                                          let uu____9936 =
                                            let uu____9943 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____9943) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____9936 in
                                        FStar_Syntax_Syntax.mk uu____9935 in
                                      uu____9932 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____9951 =
                                      let uu____9954 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____9954] in
                                    (uu____9929, uu____9951) in
                                  FStar_Pervasives_Native.Some uu____9920
                              | (uu____9967,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9969)) ->
                                  let uu____9974 =
                                    let uu____9981 =
                                      let uu____9984 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____9984] in
                                    (t11, uu____9981) in
                                  FStar_Pervasives_Native.Some uu____9974
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9994),uu____9995) ->
                                  let uu____10000 =
                                    let uu____10007 =
                                      let uu____10010 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10010] in
                                    (t21, uu____10007) in
                                  FStar_Pervasives_Native.Some uu____10000
                              | uu____10019 ->
                                  let uu____10024 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10024 with
                                   | (head1,uu____10048) ->
                                       let uu____10069 =
                                         let uu____10070 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10070.FStar_Syntax_Syntax.n in
                                       (match uu____10069 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10081;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10083;_}
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
                                        | uu____10090 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10103) ->
                  let uu____10128 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___238_10154  ->
                            match uu___238_10154 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10161 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10161 with
                                      | (u',uu____10177) ->
                                          let uu____10198 =
                                            let uu____10199 = whnf env u' in
                                            uu____10199.FStar_Syntax_Syntax.n in
                                          (match uu____10198 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10203) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10228 -> false))
                                 | uu____10229 -> false)
                            | uu____10232 -> false)) in
                  (match uu____10128 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10266 tps =
                         match uu____10266 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10314 =
                                    let uu____10323 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10323 in
                                  (match uu____10314 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10358 -> FStar_Pervasives_Native.None) in
                       let uu____10367 =
                         let uu____10376 =
                           let uu____10383 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10383, []) in
                         make_lower_bound uu____10376 lower_bounds in
                       (match uu____10367 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10395 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10395
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
                            ((let uu____10415 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10415
                              then
                                let wl' =
                                  let uu___266_10417 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___266_10417.wl_deferred);
                                    ctr = (uu___266_10417.ctr);
                                    defer_ok = (uu___266_10417.defer_ok);
                                    smt_ok = (uu___266_10417.smt_ok);
                                    tcenv = (uu___266_10417.tcenv)
                                  } in
                                let uu____10418 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10418
                              else ());
                             (let uu____10420 =
                                solve_t env eq_prob
                                  (let uu___267_10422 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___267_10422.wl_deferred);
                                     ctr = (uu___267_10422.ctr);
                                     defer_ok = (uu___267_10422.defer_ok);
                                     smt_ok = (uu___267_10422.smt_ok);
                                     tcenv = (uu___267_10422.tcenv)
                                   }) in
                              match uu____10420 with
                              | Success uu____10425 ->
                                  let wl1 =
                                    let uu___268_10427 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___268_10427.wl_deferred);
                                      ctr = (uu___268_10427.ctr);
                                      defer_ok = (uu___268_10427.defer_ok);
                                      smt_ok = (uu___268_10427.smt_ok);
                                      tcenv = (uu___268_10427.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10429 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10434 -> FStar_Pervasives_Native.None))))
              | uu____10435 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10444 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10444
         then
           let uu____10445 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10445
         else ());
        (let uu____10447 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10447 with
         | (u,args) ->
             let uu____10486 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10486 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10527 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10527 with
                    | (h1,args1) ->
                        let uu____10568 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10568 with
                         | (h2,uu____10588) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10615 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10615
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10633 =
                                          let uu____10636 =
                                            let uu____10637 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10637 in
                                          [uu____10636] in
                                        FStar_Pervasives_Native.Some
                                          uu____10633))
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
                                       (let uu____10670 =
                                          let uu____10673 =
                                            let uu____10674 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10674 in
                                          [uu____10673] in
                                        FStar_Pervasives_Native.Some
                                          uu____10670))
                                  else FStar_Pervasives_Native.None
                              | uu____10688 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10778 =
                               let uu____10787 =
                                 let uu____10790 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10790 in
                               (uu____10787, m1) in
                             FStar_Pervasives_Native.Some uu____10778)
                    | (uu____10803,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10805)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____10853),uu____10854) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____10901 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10954) ->
                       let uu____10979 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___239_11005  ->
                                 match uu___239_11005 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11012 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11012 with
                                           | (u',uu____11028) ->
                                               let uu____11049 =
                                                 let uu____11050 =
                                                   whnf env u' in
                                                 uu____11050.FStar_Syntax_Syntax.n in
                                               (match uu____11049 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11054) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11079 -> false))
                                      | uu____11080 -> false)
                                 | uu____11083 -> false)) in
                       (match uu____10979 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11121 tps =
                              match uu____11121 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11183 =
                                         let uu____11194 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11194 in
                                       (match uu____11183 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11245 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11256 =
                              let uu____11267 =
                                let uu____11276 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11276, []) in
                              make_upper_bound uu____11267 upper_bounds in
                            (match uu____11256 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11290 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11290
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
                                 ((let uu____11316 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11316
                                   then
                                     let wl' =
                                       let uu___269_11318 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___269_11318.wl_deferred);
                                         ctr = (uu___269_11318.ctr);
                                         defer_ok = (uu___269_11318.defer_ok);
                                         smt_ok = (uu___269_11318.smt_ok);
                                         tcenv = (uu___269_11318.tcenv)
                                       } in
                                     let uu____11319 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11319
                                   else ());
                                  (let uu____11321 =
                                     solve_t env eq_prob
                                       (let uu___270_11323 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___270_11323.wl_deferred);
                                          ctr = (uu___270_11323.ctr);
                                          defer_ok =
                                            (uu___270_11323.defer_ok);
                                          smt_ok = (uu___270_11323.smt_ok);
                                          tcenv = (uu___270_11323.tcenv)
                                        }) in
                                   match uu____11321 with
                                   | Success uu____11326 ->
                                       let wl1 =
                                         let uu___271_11328 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___271_11328.wl_deferred);
                                           ctr = (uu___271_11328.ctr);
                                           defer_ok =
                                             (uu___271_11328.defer_ok);
                                           smt_ok = (uu___271_11328.smt_ok);
                                           tcenv = (uu___271_11328.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11330 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11335 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11336 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11411 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11411
                      then
                        let uu____11412 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11412
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___272_11466 = hd1 in
                      let uu____11467 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___272_11466.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___272_11466.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11467
                      } in
                    let hd21 =
                      let uu___273_11471 = hd2 in
                      let uu____11472 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___273_11471.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___273_11471.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11472
                      } in
                    let prob =
                      let uu____11476 =
                        let uu____11481 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11481 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11476 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11492 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11492 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11496 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11496 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11534 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11539 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11534 uu____11539 in
                         ((let uu____11549 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11549
                           then
                             let uu____11550 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11551 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11550 uu____11551
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11574 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11584 = aux scope env [] bs1 bs2 in
              match uu____11584 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11608 = compress_tprob wl problem in
        solve_t' env uu____11608 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11641 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11641 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11672,uu____11673) ->
                   let rec may_relate head3 =
                     let uu____11698 =
                       let uu____11699 = FStar_Syntax_Subst.compress head3 in
                       uu____11699.FStar_Syntax_Syntax.n in
                     match uu____11698 with
                     | FStar_Syntax_Syntax.Tm_name uu____11702 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11703 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11726;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11727;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11730;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11731;
                           FStar_Syntax_Syntax.fv_qual = uu____11732;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11736,uu____11737) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11779) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11785) ->
                         may_relate t
                     | uu____11790 -> false in
                   let uu____11791 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11791
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
                                let uu____11808 =
                                  let uu____11809 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11809 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11808 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11811 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11811
                   else
                     (let uu____11813 =
                        let uu____11814 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11815 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11814 uu____11815 in
                      giveup env1 uu____11813 orig)
               | (uu____11816,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___274_11830 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___274_11830.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___274_11830.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___274_11830.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___274_11830.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___274_11830.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___274_11830.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___274_11830.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___274_11830.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____11831,FStar_Pervasives_Native.None ) ->
                   ((let uu____11843 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____11843
                     then
                       let uu____11844 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11845 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____11846 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____11847 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____11844
                         uu____11845 uu____11846 uu____11847
                     else ());
                    (let uu____11849 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____11849 with
                     | (head11,args1) ->
                         let uu____11886 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____11886 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____11940 =
                                  let uu____11941 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____11942 = args_to_string args1 in
                                  let uu____11943 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____11944 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____11941 uu____11942 uu____11943
                                    uu____11944 in
                                giveup env1 uu____11940 orig
                              else
                                (let uu____11946 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____11952 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____11952 = FStar_Syntax_Util.Equal) in
                                 if uu____11946
                                 then
                                   let uu____11953 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____11953 with
                                   | USolved wl2 ->
                                       let uu____11955 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____11955
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____11959 =
                                      base_and_refinement env1 t1 in
                                    match uu____11959 with
                                    | (base1,refinement1) ->
                                        let uu____11996 =
                                          base_and_refinement env1 t2 in
                                        (match uu____11996 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12077 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12077 with
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
                                                           (fun uu____12099 
                                                              ->
                                                              fun uu____12100
                                                                 ->
                                                                match 
                                                                  (uu____12099,
                                                                    uu____12100)
                                                                with
                                                                | ((a,uu____12118),
                                                                   (a',uu____12120))
                                                                    ->
                                                                    let uu____12129
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
                                                                    uu____12129)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12139 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12139 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12145 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___275_12193 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___275_12193.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12232 =
          match uu____12232 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12448  ->
                              match uu____12448 with
                              | (x,imp) ->
                                  let uu____12459 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12459, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12472 = FStar_Syntax_Util.type_u () in
                      match uu____12472 with
                      | (t1,uu____12478) ->
                          let uu____12479 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12479 in
                    let uu____12484 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12484 with
                     | (t',tm_u1) ->
                         let uu____12497 = destruct_flex_t t' in
                         (match uu____12497 with
                          | (uu____12534,u1,k1,uu____12537) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12596 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12596 in
                              let sol =
                                let uu____12600 =
                                  let uu____12609 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12609) in
                                TERM uu____12600 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____12745 = pat_var_opt env pat_args hd1 in
                    (match uu____12745 with
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
                                    (fun uu____12808  ->
                                       match uu____12808 with
                                       | (x,uu____12814) ->
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
                            let uu____12829 =
                              let uu____12830 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____12830 in
                            if uu____12829
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____12842 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____12842 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____12857::uu____12858) ->
                    let uu____12889 =
                      let uu____12902 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____12902 in
                    (match uu____12889 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____12941 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____12948::uu____12949,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____12984 =
                let uu____12997 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____12997 in
              (match uu____12984 with
               | (all_formals,res_t) ->
                   let uu____13022 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____13022 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13056 = lhs in
          match uu____13056 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13066 ->
                    let uu____13067 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13067 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13090 = p in
          match uu____13090 with
          | (((u,k),xs,c),ps,(h,uu____13101,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13183 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13183 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13206 = h gs_xs in
                     let uu____13207 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13206 uu____13207 in
                   ((let uu____13213 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13213
                     then
                       let uu____13214 =
                         let uu____13217 =
                           let uu____13218 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13218
                             (FStar_String.concat "\n\t") in
                         let uu____13223 =
                           let uu____13226 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13227 =
                             let uu____13230 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13231 =
                               let uu____13234 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13235 =
                                 let uu____13238 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13239 =
                                   let uu____13242 =
                                     let uu____13243 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13243
                                       (FStar_String.concat ", ") in
                                   let uu____13248 =
                                     let uu____13251 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13251] in
                                   uu____13242 :: uu____13248 in
                                 uu____13238 :: uu____13239 in
                               uu____13234 :: uu____13235 in
                             uu____13230 :: uu____13231 in
                           uu____13226 :: uu____13227 in
                         uu____13217 :: uu____13223 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13214
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___240_13272 =
          match uu___240_13272 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13304 = p in
          match uu____13304 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13395 = FStar_List.nth ps i in
              (match uu____13395 with
               | (pi,uu____13399) ->
                   let uu____13404 = FStar_List.nth xs i in
                   (match uu____13404 with
                    | (xi,uu____13416) ->
                        let rec gs k =
                          let uu____13429 =
                            let uu____13442 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13442 in
                          match uu____13429 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13517)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13530 = new_uvar r xs k_a in
                                    (match uu____13530 with
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
                                         let uu____13552 = aux subst2 tl1 in
                                         (match uu____13552 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13579 =
                                                let uu____13582 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13582 :: gi_xs' in
                                              let uu____13583 =
                                                let uu____13586 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13586 :: gi_ps' in
                                              (uu____13579, uu____13583))) in
                              aux [] bs in
                        let uu____13591 =
                          let uu____13592 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13592 in
                        if uu____13591
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13596 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13596 with
                           | (g_xs,uu____13608) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13619 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13620 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13619
                                   uu____13620 in
                               let sub1 =
                                 let uu____13626 =
                                   let uu____13631 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13634 =
                                     let uu____13637 =
                                       FStar_List.map
                                         (fun uu____13652  ->
                                            match uu____13652 with
                                            | (uu____13661,uu____13662,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13637 in
                                   mk_problem (p_scope orig) orig uu____13631
                                     (p_rel orig) uu____13634
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13626 in
                               ((let uu____13677 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13677
                                 then
                                   let uu____13678 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13679 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13678 uu____13679
                                 else ());
                                (let wl2 =
                                   let uu____13682 =
                                     let uu____13685 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13685 in
                                   solve_prob orig uu____13682
                                     [TERM (u, proj)] wl1 in
                                 let uu____13694 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13694))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13725 = lhs in
          match uu____13725 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13761 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13761 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13794 =
                        let uu____13841 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13841) in
                      FStar_Pervasives_Native.Some uu____13794
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____13985 =
                           let uu____13992 =
                             let uu____13993 = FStar_Syntax_Subst.compress k1 in
                             uu____13993.FStar_Syntax_Syntax.n in
                           (uu____13992, args) in
                         match uu____13985 with
                         | (uu____14004,[]) ->
                             let uu____14007 =
                               let uu____14018 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14018) in
                             FStar_Pervasives_Native.Some uu____14007
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14039,uu____14040) ->
                             let uu____14061 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14061 with
                              | (uv1,uv_args) ->
                                  let uu____14104 =
                                    let uu____14105 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14105.FStar_Syntax_Syntax.n in
                                  (match uu____14104 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14115) ->
                                       let uu____14140 =
                                         pat_vars env [] uv_args in
                                       (match uu____14140 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14167  ->
                                                      let uu____14168 =
                                                        let uu____14169 =
                                                          let uu____14170 =
                                                            let uu____14175 =
                                                              let uu____14176
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14176
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14175 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14170 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14169 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14168)) in
                                            let c1 =
                                              let uu____14186 =
                                                let uu____14187 =
                                                  let uu____14192 =
                                                    let uu____14193 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14193
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14192 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14187 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14186 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14206 =
                                                let uu____14209 =
                                                  let uu____14210 =
                                                    let uu____14213 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14213
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14210 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14209 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14206 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14231 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14236,uu____14237) ->
                             let uu____14256 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14256 with
                              | (uv1,uv_args) ->
                                  let uu____14299 =
                                    let uu____14300 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14300.FStar_Syntax_Syntax.n in
                                  (match uu____14299 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14310) ->
                                       let uu____14335 =
                                         pat_vars env [] uv_args in
                                       (match uu____14335 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14362  ->
                                                      let uu____14363 =
                                                        let uu____14364 =
                                                          let uu____14365 =
                                                            let uu____14370 =
                                                              let uu____14371
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14371
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14370 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14365 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14364 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14363)) in
                                            let c1 =
                                              let uu____14381 =
                                                let uu____14382 =
                                                  let uu____14387 =
                                                    let uu____14388 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14388
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14387 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14382 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14381 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14401 =
                                                let uu____14404 =
                                                  let uu____14405 =
                                                    let uu____14408 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14408
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14405 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14404 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14401 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14426 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14433) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14474 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14474
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14510 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14510 with
                                  | (args1,rest) ->
                                      let uu____14539 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14539 with
                                       | (xs2,c2) ->
                                           let uu____14552 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14552
                                             (fun uu____14576  ->
                                                match uu____14576 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14616 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14616 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14684 =
                                        let uu____14689 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14689 in
                                      FStar_All.pipe_right uu____14684
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14704 ->
                             let uu____14711 =
                               let uu____14712 =
                                 let uu____14717 =
                                   let uu____14718 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14719 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14720 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14718 uu____14719 uu____14720 in
                                 (uu____14717, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14712 in
                             FStar_Exn.raise uu____14711 in
                       let uu____14727 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14727
                         (fun uu____14782  ->
                            match uu____14782 with
                            | (xs1,c1) ->
                                let uu____14831 =
                                  let uu____14872 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____14872) in
                                FStar_Pervasives_Native.Some uu____14831)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____14993 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15009 = project orig env wl1 i st in
                     match uu____15009 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15023) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15038 = imitate orig env wl1 st in
                  match uu____15038 with
                  | Failed uu____15043 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15074 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15074 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____15099 =
                      let uu____15100 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____15100 wl2 in
                    (match uu____15099 with
                     | Failed uu____15101 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____15119 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15119 with
                | (hd1,uu____15135) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15156 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15169 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15170 -> true
                     | uu____15187 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15191 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15191
                         then true
                         else
                           ((let uu____15194 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15194
                             then
                               let uu____15195 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15195
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15215 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15215 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15228 =
                            let uu____15229 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15229 in
                          giveup_or_defer1 orig uu____15228
                        else
                          (let uu____15231 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15231
                           then
                             let uu____15232 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15232
                              then
                                let uu____15233 = subterms args_lhs in
                                imitate' orig env wl1 uu____15233
                              else
                                ((let uu____15238 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15238
                                  then
                                    let uu____15239 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15240 = names_to_string fvs1 in
                                    let uu____15241 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15239 uu____15240 uu____15241
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
                               (let uu____15245 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15245
                                then
                                  ((let uu____15247 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15247
                                    then
                                      let uu____15248 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15249 = names_to_string fvs1 in
                                      let uu____15250 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15248 uu____15249 uu____15250
                                    else ());
                                   (let uu____15252 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15252))
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
                     (let uu____15263 =
                        let uu____15264 = FStar_Syntax_Free.names t1 in
                        check_head uu____15264 t2 in
                      if uu____15263
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15275 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15275
                          then
                            let uu____15276 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15277 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15276 uu____15277
                          else ());
                         (let uu____15285 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15285))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15362 uu____15363 r =
               match (uu____15362, uu____15363) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15561 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15561
                   then
                     let uu____15562 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15562
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15586 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15586
                       then
                         let uu____15587 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15588 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15589 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15590 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15591 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15587 uu____15588 uu____15589 uu____15590
                           uu____15591
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15651 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15651 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15665 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15665 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15719 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15719 in
                                  let uu____15722 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15722 k3)
                           else
                             (let uu____15726 =
                                let uu____15727 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15728 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15729 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15727 uu____15728 uu____15729 in
                              failwith uu____15726) in
                       let uu____15730 =
                         let uu____15737 =
                           let uu____15750 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15750 in
                         match uu____15737 with
                         | (bs,k1') ->
                             let uu____15775 =
                               let uu____15788 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15788 in
                             (match uu____15775 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15816 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15816 in
                                  let uu____15825 =
                                    let uu____15830 =
                                      let uu____15831 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15831.FStar_Syntax_Syntax.n in
                                    let uu____15834 =
                                      let uu____15835 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15835.FStar_Syntax_Syntax.n in
                                    (uu____15830, uu____15834) in
                                  (match uu____15825 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15844,uu____15845) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____15848,FStar_Syntax_Syntax.Tm_type
                                      uu____15849) -> (k2'_ys, [sub_prob])
                                   | uu____15852 ->
                                       let uu____15857 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15857 with
                                        | (t,uu____15869) ->
                                            let uu____15870 = new_uvar r zs t in
                                            (match uu____15870 with
                                             | (k_zs,uu____15882) ->
                                                 let kprob =
                                                   let uu____15884 =
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
                                                          _0_64) uu____15884 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15730 with
                       | (k_u',sub_probs) ->
                           let uu____15901 =
                             let uu____15912 =
                               let uu____15913 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15913 in
                             let uu____15922 =
                               let uu____15925 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15925 in
                             let uu____15928 =
                               let uu____15931 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15931 in
                             (uu____15912, uu____15922, uu____15928) in
                           (match uu____15901 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15950 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15950 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15969 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15969
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15973 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15973 with
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
             let solve_one_pat uu____16026 uu____16027 =
               match (uu____16026, uu____16027) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16145 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16145
                     then
                       let uu____16146 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16147 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16146 uu____16147
                     else ());
                    (let uu____16149 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16149
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16168  ->
                              fun uu____16169  ->
                                match (uu____16168, uu____16169) with
                                | ((a,uu____16187),(t21,uu____16189)) ->
                                    let uu____16198 =
                                      let uu____16203 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16203
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16198
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16209 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16209 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16224 = occurs_check env wl (u1, k1) t21 in
                        match uu____16224 with
                        | (occurs_ok,uu____16232) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16240 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16240
                            then
                              let sol =
                                let uu____16242 =
                                  let uu____16251 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16251) in
                                TERM uu____16242 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16258 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16258
                               then
                                 let uu____16259 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16259 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16283,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16309 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16309
                                       then
                                         let uu____16310 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16310
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16317 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16319 = lhs in
             match uu____16319 with
             | (t1,u1,k1,args1) ->
                 let uu____16324 = rhs in
                 (match uu____16324 with
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
                       | uu____16364 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16374 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16374 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16392) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16399 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16399
                                    then
                                      let uu____16400 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16400
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16407 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16409 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16409
        then
          let uu____16410 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16410
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16414 = FStar_Util.physical_equality t1 t2 in
           if uu____16414
           then
             let uu____16415 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16415
           else
             ((let uu____16418 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16418
               then
                 let uu____16419 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16419
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16422,uu____16423) ->
                   let uu____16450 =
                     let uu___276_16451 = problem in
                     let uu____16452 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___276_16451.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16452;
                       FStar_TypeChecker_Common.relation =
                         (uu___276_16451.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___276_16451.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___276_16451.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___276_16451.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___276_16451.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___276_16451.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___276_16451.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___276_16451.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16450 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16453,uu____16454) ->
                   let uu____16461 =
                     let uu___276_16462 = problem in
                     let uu____16463 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___276_16462.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16463;
                       FStar_TypeChecker_Common.relation =
                         (uu___276_16462.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___276_16462.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___276_16462.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___276_16462.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___276_16462.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___276_16462.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___276_16462.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___276_16462.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16461 wl
               | (uu____16464,FStar_Syntax_Syntax.Tm_ascribed uu____16465) ->
                   let uu____16492 =
                     let uu___277_16493 = problem in
                     let uu____16494 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___277_16493.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___277_16493.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___277_16493.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16494;
                       FStar_TypeChecker_Common.element =
                         (uu___277_16493.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___277_16493.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___277_16493.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___277_16493.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___277_16493.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___277_16493.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16492 wl
               | (uu____16495,FStar_Syntax_Syntax.Tm_meta uu____16496) ->
                   let uu____16503 =
                     let uu___277_16504 = problem in
                     let uu____16505 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___277_16504.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___277_16504.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___277_16504.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16505;
                       FStar_TypeChecker_Common.element =
                         (uu___277_16504.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___277_16504.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___277_16504.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___277_16504.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___277_16504.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___277_16504.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16503 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16506,uu____16507) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16508,FStar_Syntax_Syntax.Tm_bvar uu____16509) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___241_16564 =
                     match uu___241_16564 with
                     | [] -> c
                     | bs ->
                         let uu____16586 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16586 in
                   let uu____16595 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16595 with
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
                                   let uu____16737 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16737
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16739 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16739))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___242_16815 =
                     match uu___242_16815 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16849 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16849 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16985 =
                                   let uu____16990 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16991 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16990
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16991 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16985))
               | (FStar_Syntax_Syntax.Tm_abs uu____16996,uu____16997) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17022 -> true
                     | uu____17039 -> false in
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
                       (let uu____17086 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___278_17094 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___278_17094.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___278_17094.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___278_17094.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___278_17094.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___278_17094.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___278_17094.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___278_17094.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___278_17094.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___278_17094.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___278_17094.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___278_17094.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___278_17094.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___278_17094.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___278_17094.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___278_17094.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___278_17094.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___278_17094.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___278_17094.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___278_17094.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___278_17094.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___278_17094.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___278_17094.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___278_17094.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___278_17094.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___278_17094.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___278_17094.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___278_17094.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___278_17094.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___278_17094.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___278_17094.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___278_17094.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17086 with
                        | (uu____17097,ty,uu____17099) ->
                            let uu____17100 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17100) in
                   let uu____17101 =
                     let uu____17118 = maybe_eta t1 in
                     let uu____17125 = maybe_eta t2 in
                     (uu____17118, uu____17125) in
                   (match uu____17101 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___279_17167 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___279_17167.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___279_17167.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___279_17167.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___279_17167.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___279_17167.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___279_17167.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___279_17167.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___279_17167.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17190 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17190
                        then
                          let uu____17191 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17191 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17206 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17206.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17206.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17206.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17206.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17206.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17206.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17206.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17206.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17230 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17230
                        then
                          let uu____17231 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17231 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17246 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17246.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17246.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17246.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17246.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17246.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17246.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17246.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17246.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17250 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17267,FStar_Syntax_Syntax.Tm_abs uu____17268) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17293 -> true
                     | uu____17310 -> false in
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
                       (let uu____17357 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___278_17365 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___278_17365.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___278_17365.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___278_17365.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___278_17365.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___278_17365.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___278_17365.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___278_17365.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___278_17365.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___278_17365.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___278_17365.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___278_17365.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___278_17365.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___278_17365.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___278_17365.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___278_17365.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___278_17365.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___278_17365.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___278_17365.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___278_17365.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___278_17365.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___278_17365.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___278_17365.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___278_17365.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___278_17365.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___278_17365.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___278_17365.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___278_17365.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___278_17365.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___278_17365.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___278_17365.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___278_17365.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17357 with
                        | (uu____17368,ty,uu____17370) ->
                            let uu____17371 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17371) in
                   let uu____17372 =
                     let uu____17389 = maybe_eta t1 in
                     let uu____17396 = maybe_eta t2 in
                     (uu____17389, uu____17396) in
                   (match uu____17372 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___279_17438 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___279_17438.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___279_17438.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___279_17438.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___279_17438.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___279_17438.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___279_17438.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___279_17438.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___279_17438.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17461 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17461
                        then
                          let uu____17462 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17462 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17477 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17477.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17477.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17477.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17477.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17477.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17477.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17477.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17477.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17501 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17501
                        then
                          let uu____17502 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17502 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17517 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17517.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17517.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17517.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17517.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17517.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17517.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17517.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17517.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17521 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17538,FStar_Syntax_Syntax.Tm_refine uu____17539) ->
                   let uu____17552 = as_refinement env wl t1 in
                   (match uu____17552 with
                    | (x1,phi1) ->
                        let uu____17559 = as_refinement env wl t2 in
                        (match uu____17559 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17567 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17567 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17605 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17605
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17609 =
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
                                 let uu____17615 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17615 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17624 =
                                   let uu____17629 =
                                     let uu____17630 =
                                       let uu____17637 =
                                         FStar_Syntax_Syntax.mk_binder x11 in
                                       [uu____17637] in
                                     FStar_List.append (p_scope orig)
                                       uu____17630 in
                                   mk_problem uu____17629 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17624 in
                               let uu____17646 =
                                 solve env1
                                   (let uu___281_17648 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___281_17648.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___281_17648.smt_ok);
                                      tcenv = (uu___281_17648.tcenv)
                                    }) in
                               (match uu____17646 with
                                | Failed uu____17655 -> fallback ()
                                | Success uu____17660 ->
                                    let guard =
                                      let uu____17664 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17669 =
                                        let uu____17670 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17670
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17664
                                        uu____17669 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___282_17679 = wl1 in
                                      {
                                        attempting =
                                          (uu___282_17679.attempting);
                                        wl_deferred =
                                          (uu___282_17679.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___282_17679.defer_ok);
                                        smt_ok = (uu___282_17679.smt_ok);
                                        tcenv = (uu___282_17679.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17681,FStar_Syntax_Syntax.Tm_uvar uu____17682) ->
                   let uu____17715 = destruct_flex_t t1 in
                   let uu____17716 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17715 uu____17716
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17717;
                     FStar_Syntax_Syntax.pos = uu____17718;
                     FStar_Syntax_Syntax.vars = uu____17719;_},uu____17720),FStar_Syntax_Syntax.Tm_uvar
                  uu____17721) ->
                   let uu____17774 = destruct_flex_t t1 in
                   let uu____17775 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17774 uu____17775
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17776,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17777;
                     FStar_Syntax_Syntax.pos = uu____17778;
                     FStar_Syntax_Syntax.vars = uu____17779;_},uu____17780))
                   ->
                   let uu____17833 = destruct_flex_t t1 in
                   let uu____17834 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17833 uu____17834
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17835;
                     FStar_Syntax_Syntax.pos = uu____17836;
                     FStar_Syntax_Syntax.vars = uu____17837;_},uu____17838),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17839;
                     FStar_Syntax_Syntax.pos = uu____17840;
                     FStar_Syntax_Syntax.vars = uu____17841;_},uu____17842))
                   ->
                   let uu____17915 = destruct_flex_t t1 in
                   let uu____17916 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17915 uu____17916
               | (FStar_Syntax_Syntax.Tm_uvar uu____17917,uu____17918) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17935 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17935 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17942;
                     FStar_Syntax_Syntax.pos = uu____17943;
                     FStar_Syntax_Syntax.vars = uu____17944;_},uu____17945),uu____17946)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17983 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17983 t2 wl
               | (uu____17990,FStar_Syntax_Syntax.Tm_uvar uu____17991) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18008,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18009;
                     FStar_Syntax_Syntax.pos = uu____18010;
                     FStar_Syntax_Syntax.vars = uu____18011;_},uu____18012))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18049,FStar_Syntax_Syntax.Tm_type uu____18050) ->
                   solve_t' env
                     (let uu___283_18068 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_18068.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_18068.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_18068.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_18068.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_18068.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_18068.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_18068.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_18068.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_18068.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18069;
                     FStar_Syntax_Syntax.pos = uu____18070;
                     FStar_Syntax_Syntax.vars = uu____18071;_},uu____18072),FStar_Syntax_Syntax.Tm_type
                  uu____18073) ->
                   solve_t' env
                     (let uu___283_18111 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_18111.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_18111.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_18111.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_18111.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_18111.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_18111.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_18111.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_18111.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_18111.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18112,FStar_Syntax_Syntax.Tm_arrow uu____18113) ->
                   solve_t' env
                     (let uu___283_18143 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_18143.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_18143.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_18143.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_18143.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_18143.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_18143.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_18143.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_18143.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_18143.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18144;
                     FStar_Syntax_Syntax.pos = uu____18145;
                     FStar_Syntax_Syntax.vars = uu____18146;_},uu____18147),FStar_Syntax_Syntax.Tm_arrow
                  uu____18148) ->
                   solve_t' env
                     (let uu___283_18198 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_18198.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_18198.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_18198.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_18198.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_18198.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_18198.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_18198.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_18198.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_18198.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18199,uu____18200) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18219 =
                        let uu____18220 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18220 in
                      if uu____18219
                      then
                        let uu____18221 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___284_18227 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___284_18227.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___284_18227.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___284_18227.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___284_18227.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___284_18227.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___284_18227.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___284_18227.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___284_18227.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___284_18227.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18228 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18221 uu____18228 t2
                          wl
                      else
                        (let uu____18236 = base_and_refinement env t2 in
                         match uu____18236 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18279 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___285_18285 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___285_18285.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___285_18285.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___285_18285.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___285_18285.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___285_18285.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___285_18285.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___285_18285.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___285_18285.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___285_18285.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18286 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18279
                                    uu____18286 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___286_18306 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___286_18306.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___286_18306.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18309 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18309 in
                                  let guard =
                                    let uu____18321 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18321
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18329;
                     FStar_Syntax_Syntax.pos = uu____18330;
                     FStar_Syntax_Syntax.vars = uu____18331;_},uu____18332),uu____18333)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18372 =
                        let uu____18373 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18373 in
                      if uu____18372
                      then
                        let uu____18374 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___284_18380 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___284_18380.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___284_18380.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___284_18380.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___284_18380.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___284_18380.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___284_18380.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___284_18380.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___284_18380.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___284_18380.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18381 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18374 uu____18381 t2
                          wl
                      else
                        (let uu____18389 = base_and_refinement env t2 in
                         match uu____18389 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18432 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___285_18438 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___285_18438.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___285_18438.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___285_18438.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___285_18438.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___285_18438.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___285_18438.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___285_18438.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___285_18438.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___285_18438.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18439 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18432
                                    uu____18439 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___286_18459 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___286_18459.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___286_18459.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18462 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18462 in
                                  let guard =
                                    let uu____18474 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18474
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18482,FStar_Syntax_Syntax.Tm_uvar uu____18483) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18501 = base_and_refinement env t1 in
                      match uu____18501 with
                      | (t_base,uu____18517) ->
                          solve_t env
                            (let uu___287_18539 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___287_18539.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___287_18539.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___287_18539.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___287_18539.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___287_18539.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___287_18539.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___287_18539.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___287_18539.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18542,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18543;
                     FStar_Syntax_Syntax.pos = uu____18544;
                     FStar_Syntax_Syntax.vars = uu____18545;_},uu____18546))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18584 = base_and_refinement env t1 in
                      match uu____18584 with
                      | (t_base,uu____18600) ->
                          solve_t env
                            (let uu___287_18622 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___287_18622.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___287_18622.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___287_18622.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___287_18622.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___287_18622.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___287_18622.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___287_18622.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___287_18622.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18625,uu____18626) ->
                   let t21 =
                     let uu____18636 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18636 in
                   solve_t env
                     (let uu___288_18660 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___288_18660.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___288_18660.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___288_18660.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___288_18660.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___288_18660.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___288_18660.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___288_18660.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___288_18660.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___288_18660.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18661,FStar_Syntax_Syntax.Tm_refine uu____18662) ->
                   let t11 =
                     let uu____18672 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18672 in
                   solve_t env
                     (let uu___289_18696 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___289_18696.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___289_18696.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___289_18696.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___289_18696.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___289_18696.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___289_18696.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___289_18696.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___289_18696.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___289_18696.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18699,uu____18700) ->
                   let head1 =
                     let uu____18726 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18726
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18770 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18770
                       FStar_Pervasives_Native.fst in
                   let uu____18811 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18811
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18826 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18826
                      then
                        let guard =
                          let uu____18838 =
                            let uu____18839 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18839 = FStar_Syntax_Util.Equal in
                          if uu____18838
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18843 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18843) in
                        let uu____18846 = solve_prob orig guard [] wl in
                        solve env uu____18846
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18849,uu____18850) ->
                   let head1 =
                     let uu____18860 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18860
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18904 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18904
                       FStar_Pervasives_Native.fst in
                   let uu____18945 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18945
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18960 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18960
                      then
                        let guard =
                          let uu____18972 =
                            let uu____18973 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18973 = FStar_Syntax_Util.Equal in
                          if uu____18972
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18977 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18977) in
                        let uu____18980 = solve_prob orig guard [] wl in
                        solve env uu____18980
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18983,uu____18984) ->
                   let head1 =
                     let uu____18988 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18988
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19032 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19032
                       FStar_Pervasives_Native.fst in
                   let uu____19073 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19073
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19088 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19088
                      then
                        let guard =
                          let uu____19100 =
                            let uu____19101 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19101 = FStar_Syntax_Util.Equal in
                          if uu____19100
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19105 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19105) in
                        let uu____19108 = solve_prob orig guard [] wl in
                        solve env uu____19108
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19111,uu____19112) ->
                   let head1 =
                     let uu____19116 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19116
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19160 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19160
                       FStar_Pervasives_Native.fst in
                   let uu____19201 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19201
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19216 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19216
                      then
                        let guard =
                          let uu____19228 =
                            let uu____19229 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19229 = FStar_Syntax_Util.Equal in
                          if uu____19228
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19233 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19233) in
                        let uu____19236 = solve_prob orig guard [] wl in
                        solve env uu____19236
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19239,uu____19240) ->
                   let head1 =
                     let uu____19244 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19244
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19288 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19288
                       FStar_Pervasives_Native.fst in
                   let uu____19329 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19329
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19344 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19344
                      then
                        let guard =
                          let uu____19356 =
                            let uu____19357 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19357 = FStar_Syntax_Util.Equal in
                          if uu____19356
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19361 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19361) in
                        let uu____19364 = solve_prob orig guard [] wl in
                        solve env uu____19364
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19367,uu____19368) ->
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
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19503) in
                        let uu____19506 = solve_prob orig guard [] wl in
                        solve env uu____19506
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19509,FStar_Syntax_Syntax.Tm_match uu____19510) ->
                   let head1 =
                     let uu____19536 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19536
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19580 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19580
                       FStar_Pervasives_Native.fst in
                   let uu____19621 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19621
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19636 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19636
                      then
                        let guard =
                          let uu____19648 =
                            let uu____19649 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19649 = FStar_Syntax_Util.Equal in
                          if uu____19648
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19653 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19653) in
                        let uu____19656 = solve_prob orig guard [] wl in
                        solve env uu____19656
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19659,FStar_Syntax_Syntax.Tm_uinst uu____19660) ->
                   let head1 =
                     let uu____19670 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19670
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19714 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19714
                       FStar_Pervasives_Native.fst in
                   let uu____19755 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19755
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19770 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19770
                      then
                        let guard =
                          let uu____19782 =
                            let uu____19783 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19783 = FStar_Syntax_Util.Equal in
                          if uu____19782
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19787 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19787) in
                        let uu____19790 = solve_prob orig guard [] wl in
                        solve env uu____19790
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19793,FStar_Syntax_Syntax.Tm_name uu____19794) ->
                   let head1 =
                     let uu____19798 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19798
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19842 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19842
                       FStar_Pervasives_Native.fst in
                   let uu____19883 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19883
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19898 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19898
                      then
                        let guard =
                          let uu____19910 =
                            let uu____19911 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19911 = FStar_Syntax_Util.Equal in
                          if uu____19910
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19915 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19915) in
                        let uu____19918 = solve_prob orig guard [] wl in
                        solve env uu____19918
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19921,FStar_Syntax_Syntax.Tm_constant uu____19922) ->
                   let head1 =
                     let uu____19926 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19926
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19970 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19970
                       FStar_Pervasives_Native.fst in
                   let uu____20011 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20011
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20026 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20026
                      then
                        let guard =
                          let uu____20038 =
                            let uu____20039 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20039 = FStar_Syntax_Util.Equal in
                          if uu____20038
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20043 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20043) in
                        let uu____20046 = solve_prob orig guard [] wl in
                        solve env uu____20046
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20049,FStar_Syntax_Syntax.Tm_fvar uu____20050) ->
                   let head1 =
                     let uu____20054 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20054
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20098 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20098
                       FStar_Pervasives_Native.fst in
                   let uu____20139 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20139
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20154 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20154
                      then
                        let guard =
                          let uu____20166 =
                            let uu____20167 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20167 = FStar_Syntax_Util.Equal in
                          if uu____20166
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20171 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20171) in
                        let uu____20174 = solve_prob orig guard [] wl in
                        solve env uu____20174
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20177,FStar_Syntax_Syntax.Tm_app uu____20178) ->
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
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20313) in
                        let uu____20316 = solve_prob orig guard [] wl in
                        solve env uu____20316
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20319,uu____20320) ->
                   let uu____20333 =
                     let uu____20334 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20335 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20334
                       uu____20335 in
                   failwith uu____20333
               | (FStar_Syntax_Syntax.Tm_delayed uu____20336,uu____20337) ->
                   let uu____20362 =
                     let uu____20363 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20364 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20363
                       uu____20364 in
                   failwith uu____20362
               | (uu____20365,FStar_Syntax_Syntax.Tm_delayed uu____20366) ->
                   let uu____20391 =
                     let uu____20392 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20393 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20392
                       uu____20393 in
                   failwith uu____20391
               | (uu____20394,FStar_Syntax_Syntax.Tm_let uu____20395) ->
                   let uu____20408 =
                     let uu____20409 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20410 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20409
                       uu____20410 in
                   failwith uu____20408
               | uu____20411 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20447 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20447
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20449 =
               let uu____20450 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20451 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20450 uu____20451 in
             giveup env uu____20449 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20471  ->
                    fun uu____20472  ->
                      match (uu____20471, uu____20472) with
                      | ((a1,uu____20490),(a2,uu____20492)) ->
                          let uu____20501 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20501)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20511 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20511 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20535 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20542)::[] -> wp1
              | uu____20559 ->
                  let uu____20568 =
                    let uu____20569 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20569 in
                  failwith uu____20568 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20577 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____20577]
              | x -> x in
            let uu____20579 =
              let uu____20588 =
                let uu____20589 =
                  let uu____20590 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20590 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20589 in
              [uu____20588] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20579;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20591 = lift_c1 () in solve_eq uu____20591 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___243_20597  ->
                       match uu___243_20597 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20598 -> false)) in
             let uu____20599 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20633)::uu____20634,(wp2,uu____20636)::uu____20637)
                   -> (wp1, wp2)
               | uu____20694 ->
                   let uu____20715 =
                     let uu____20716 =
                       let uu____20721 =
                         let uu____20722 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20723 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20722 uu____20723 in
                       (uu____20721, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20716 in
                   FStar_Exn.raise uu____20715 in
             match uu____20599 with
             | (wpc1,wpc2) ->
                 let uu____20742 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20742
                 then
                   let uu____20745 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20745 wl
                 else
                   (let uu____20749 =
                      let uu____20756 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20756 in
                    match uu____20749 with
                    | (c2_decl,qualifiers) ->
                        let uu____20777 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20777
                        then
                          let c1_repr =
                            let uu____20781 =
                              let uu____20782 =
                                let uu____20783 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20783 in
                              let uu____20784 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20782 uu____20784 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20781 in
                          let c2_repr =
                            let uu____20786 =
                              let uu____20787 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20788 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20787 uu____20788 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20786 in
                          let prob =
                            let uu____20790 =
                              let uu____20795 =
                                let uu____20796 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20797 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20796
                                  uu____20797 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20795 in
                            FStar_TypeChecker_Common.TProb uu____20790 in
                          let wl1 =
                            let uu____20799 =
                              let uu____20802 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20802 in
                            solve_prob orig uu____20799 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20811 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20811
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____20814 =
                                     let uu____20817 =
                                       let uu____20818 =
                                         let uu____20833 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20834 =
                                           let uu____20837 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20838 =
                                             let uu____20841 =
                                               let uu____20842 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20842 in
                                             [uu____20841] in
                                           uu____20837 :: uu____20838 in
                                         (uu____20833, uu____20834) in
                                       FStar_Syntax_Syntax.Tm_app uu____20818 in
                                     FStar_Syntax_Syntax.mk uu____20817 in
                                   uu____20814 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____20851 =
                                    let uu____20854 =
                                      let uu____20855 =
                                        let uu____20870 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20871 =
                                          let uu____20874 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20875 =
                                            let uu____20878 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20879 =
                                              let uu____20882 =
                                                let uu____20883 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20883 in
                                              [uu____20882] in
                                            uu____20878 :: uu____20879 in
                                          uu____20874 :: uu____20875 in
                                        (uu____20870, uu____20871) in
                                      FStar_Syntax_Syntax.Tm_app uu____20855 in
                                    FStar_Syntax_Syntax.mk uu____20854 in
                                  uu____20851 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20890 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20890 in
                           let wl1 =
                             let uu____20900 =
                               let uu____20903 =
                                 let uu____20906 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20906 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20903 in
                             solve_prob orig uu____20900 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20919 = FStar_Util.physical_equality c1 c2 in
        if uu____20919
        then
          let uu____20920 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20920
        else
          ((let uu____20923 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20923
            then
              let uu____20924 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20925 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20924
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20925
            else ());
           (let uu____20927 =
              let uu____20932 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20933 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20932, uu____20933) in
            match uu____20927 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20937),FStar_Syntax_Syntax.Total
                    (t2,uu____20939)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20956 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20956 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20959,FStar_Syntax_Syntax.Total uu____20960) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20978),FStar_Syntax_Syntax.Total
                    (t2,uu____20980)) ->
                     let uu____20997 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20997 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21001),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21003)) ->
                     let uu____21020 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21020 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21024),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21026)) ->
                     let uu____21043 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21043 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21046,FStar_Syntax_Syntax.Comp uu____21047) ->
                     let uu____21056 =
                       let uu___290_21061 = problem in
                       let uu____21066 =
                         let uu____21067 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21067 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___290_21061.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21066;
                         FStar_TypeChecker_Common.relation =
                           (uu___290_21061.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___290_21061.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___290_21061.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___290_21061.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___290_21061.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___290_21061.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___290_21061.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___290_21061.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21056 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21068,FStar_Syntax_Syntax.Comp uu____21069) ->
                     let uu____21078 =
                       let uu___290_21083 = problem in
                       let uu____21088 =
                         let uu____21089 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21089 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___290_21083.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21088;
                         FStar_TypeChecker_Common.relation =
                           (uu___290_21083.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___290_21083.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___290_21083.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___290_21083.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___290_21083.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___290_21083.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___290_21083.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___290_21083.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21078 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21090,FStar_Syntax_Syntax.GTotal uu____21091) ->
                     let uu____21100 =
                       let uu___291_21105 = problem in
                       let uu____21110 =
                         let uu____21111 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21111 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___291_21105.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___291_21105.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___291_21105.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21110;
                         FStar_TypeChecker_Common.element =
                           (uu___291_21105.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___291_21105.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___291_21105.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___291_21105.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___291_21105.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___291_21105.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21100 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21112,FStar_Syntax_Syntax.Total uu____21113) ->
                     let uu____21122 =
                       let uu___291_21127 = problem in
                       let uu____21132 =
                         let uu____21133 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21133 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___291_21127.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___291_21127.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___291_21127.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21132;
                         FStar_TypeChecker_Common.element =
                           (uu___291_21127.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___291_21127.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___291_21127.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___291_21127.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___291_21127.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___291_21127.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21122 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21134,FStar_Syntax_Syntax.Comp uu____21135) ->
                     let uu____21136 =
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
                     if uu____21136
                     then
                       let uu____21137 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21137 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21143 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21153 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21154 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21153, uu____21154)) in
                          match uu____21143 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21161 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21161
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21163 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21163 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21166 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21168 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21168) in
                                if uu____21166
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
                                  (let uu____21171 =
                                     let uu____21172 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21173 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21172 uu____21173 in
                                   giveup env uu____21171 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21178 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21216  ->
              match uu____21216 with
              | (uu____21229,uu____21230,u,uu____21232,uu____21233,uu____21234)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21178 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21265 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21265 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21283 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21311  ->
                match uu____21311 with
                | (u1,u2) ->
                    let uu____21318 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21319 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21318 uu____21319)) in
      FStar_All.pipe_right uu____21283 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21336,[])) -> "{}"
      | uu____21361 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21378 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21378
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21381 =
              FStar_List.map
                (fun uu____21391  ->
                   match uu____21391 with
                   | (uu____21396,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21381 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21401 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21401 imps
let new_t_problem:
  'Auu____21409 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21409 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21409)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21443 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21443
                then
                  let uu____21444 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21445 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21444
                    (rel_to_string rel) uu____21445
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
            let uu____21469 =
              let uu____21472 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21472 in
            FStar_Syntax_Syntax.new_bv uu____21469 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21481 =
              let uu____21484 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21484 in
            let uu____21487 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21481 uu____21487 in
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
          let uu____21517 = FStar_Options.eager_inference () in
          if uu____21517
          then
            let uu___292_21518 = probs in
            {
              attempting = (uu___292_21518.attempting);
              wl_deferred = (uu___292_21518.wl_deferred);
              ctr = (uu___292_21518.ctr);
              defer_ok = false;
              smt_ok = (uu___292_21518.smt_ok);
              tcenv = (uu___292_21518.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21529 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21529
              then
                let uu____21530 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21530
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
          ((let uu____21544 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21544
            then
              let uu____21545 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21545
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____21549 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21549
             then
               let uu____21550 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21550
             else ());
            (let f2 =
               let uu____21553 =
                 let uu____21554 = FStar_Syntax_Util.unmeta f1 in
                 uu____21554.FStar_Syntax_Syntax.n in
               match uu____21553 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21558 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___293_21559 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___293_21559.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___293_21559.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___293_21559.FStar_TypeChecker_Env.implicits)
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
            let uu____21578 =
              let uu____21579 =
                let uu____21580 =
                  let uu____21581 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21581
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21580;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21579 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21578
let with_guard_no_simp:
  'Auu____21608 .
    'Auu____21608 ->
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
            let uu____21628 =
              let uu____21629 =
                let uu____21630 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21630
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21629;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21628
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
          (let uu____21668 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21668
           then
             let uu____21669 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21670 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21669
               uu____21670
           else ());
          (let prob =
             let uu____21673 =
               let uu____21678 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21678 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21673 in
           let g =
             let uu____21686 =
               let uu____21689 = singleton' env prob smt_ok in
               solve_and_commit env uu____21689
                 (fun uu____21691  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21686 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21709 = try_teq true env t1 t2 in
        match uu____21709 with
        | FStar_Pervasives_Native.None  ->
            let uu____21712 =
              let uu____21713 =
                let uu____21718 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21719 = FStar_TypeChecker_Env.get_range env in
                (uu____21718, uu____21719) in
              FStar_Errors.Error uu____21713 in
            FStar_Exn.raise uu____21712
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21722 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21722
              then
                let uu____21723 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21724 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21725 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21723
                  uu____21724 uu____21725
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
          let uu____21739 = FStar_TypeChecker_Env.get_range env in
          let uu____21740 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21739 uu____21740
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21753 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21753
         then
           let uu____21754 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21755 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21754
             uu____21755
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21760 =
             let uu____21765 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21765 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21760 in
         let uu____21770 =
           let uu____21773 = singleton env prob in
           solve_and_commit env uu____21773
             (fun uu____21775  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21770)
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
      fun uu____21804  ->
        match uu____21804 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21843 =
                 let uu____21844 =
                   let uu____21849 =
                     let uu____21850 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21851 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21850 uu____21851 in
                   let uu____21852 = FStar_TypeChecker_Env.get_range env in
                   (uu____21849, uu____21852) in
                 FStar_Errors.Error uu____21844 in
               FStar_Exn.raise uu____21843) in
            let equiv1 v1 v' =
              let uu____21860 =
                let uu____21865 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21866 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21865, uu____21866) in
              match uu____21860 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21885 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21915 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21915 with
                      | FStar_Syntax_Syntax.U_unif uu____21922 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21951  ->
                                    match uu____21951 with
                                    | (u,v') ->
                                        let uu____21960 = equiv1 v1 v' in
                                        if uu____21960
                                        then
                                          let uu____21963 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21963 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21979 -> [])) in
            let uu____21984 =
              let wl =
                let uu___294_21988 = empty_worklist env in
                {
                  attempting = (uu___294_21988.attempting);
                  wl_deferred = (uu___294_21988.wl_deferred);
                  ctr = (uu___294_21988.ctr);
                  defer_ok = false;
                  smt_ok = (uu___294_21988.smt_ok);
                  tcenv = (uu___294_21988.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22006  ->
                      match uu____22006 with
                      | (lb,v1) ->
                          let uu____22013 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22013 with
                           | USolved wl1 -> ()
                           | uu____22015 -> fail lb v1))) in
            let rec check_ineq uu____22023 =
              match uu____22023 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22032) -> true
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
                      uu____22055,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22057,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22068) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22075,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22083 -> false) in
            let uu____22088 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22103  ->
                      match uu____22103 with
                      | (u,v1) ->
                          let uu____22110 = check_ineq (u, v1) in
                          if uu____22110
                          then true
                          else
                            ((let uu____22113 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22113
                              then
                                let uu____22114 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22115 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22114
                                  uu____22115
                              else ());
                             false))) in
            if uu____22088
            then ()
            else
              ((let uu____22119 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22119
                then
                  ((let uu____22121 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22121);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22131 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22131))
                else ());
               (let uu____22141 =
                  let uu____22142 =
                    let uu____22147 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22147) in
                  FStar_Errors.Error uu____22142 in
                FStar_Exn.raise uu____22141))
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
      let fail uu____22195 =
        match uu____22195 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22209 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22209
       then
         let uu____22210 = wl_to_string wl in
         let uu____22211 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22210 uu____22211
       else ());
      (let g1 =
         let uu____22226 = solve_and_commit env wl fail in
         match uu____22226 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___295_22239 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___295_22239.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___295_22239.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___295_22239.FStar_TypeChecker_Env.implicits)
             }
         | uu____22244 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___296_22248 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___296_22248.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___296_22248.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___296_22248.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22270 = FStar_ST.op_Bang last_proof_ns in
    match uu____22270 with
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
            let uu___297_22454 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___297_22454.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___297_22454.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___297_22454.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22455 =
            let uu____22456 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22456 in
          if uu____22455
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22464 = FStar_TypeChecker_Env.get_range env in
                     let uu____22465 =
                       let uu____22466 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22466 in
                     FStar_Errors.diag uu____22464 uu____22465)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22470 = FStar_TypeChecker_Env.get_range env in
                      let uu____22471 =
                        let uu____22472 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22472 in
                      FStar_Errors.diag uu____22470 uu____22471)
                   else ();
                   (let uu____22474 = check_trivial vc1 in
                    match uu____22474 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22481 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22482 =
                                let uu____22483 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22483 in
                              FStar_Errors.diag uu____22481 uu____22482)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22488 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22489 =
                                let uu____22490 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22490 in
                              FStar_Errors.diag uu____22488 uu____22489)
                           else ();
                           (let vcs =
                              let uu____22501 = FStar_Options.use_tactics () in
                              if uu____22501
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22520  ->
                                     (let uu____22522 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22522);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22524 =
                                   let uu____22531 = FStar_Options.peek () in
                                   (env, vc2, uu____22531) in
                                 [uu____22524]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22565  ->
                                    match uu____22565 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22576 = check_trivial goal1 in
                                        (match uu____22576 with
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
                                                (let uu____22584 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22585 =
                                                   let uu____22586 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22587 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22586 uu____22587 in
                                                 FStar_Errors.diag
                                                   uu____22584 uu____22585)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22590 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22591 =
                                                   let uu____22592 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22592 in
                                                 FStar_Errors.diag
                                                   uu____22590 uu____22591)
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
      let uu____22602 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22602 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22608 =
            let uu____22609 =
              let uu____22614 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22614) in
            FStar_Errors.Error uu____22609 in
          FStar_Exn.raise uu____22608
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22621 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22621 with
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
          let uu____22640 = FStar_Syntax_Unionfind.find u in
          match uu____22640 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22643 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22661 = acc in
          match uu____22661 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22747 = hd1 in
                   (match uu____22747 with
                    | (uu____22760,env,u,tm,k,r) ->
                        let uu____22766 = unresolved u in
                        if uu____22766
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22797 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22797
                            then
                              let uu____22798 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22799 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22800 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22798 uu____22799 uu____22800
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___298_22803 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___298_22803.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___298_22803.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___298_22803.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___298_22803.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___298_22803.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___298_22803.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___298_22803.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___298_22803.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___298_22803.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___298_22803.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___298_22803.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___298_22803.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___298_22803.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___298_22803.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___298_22803.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___298_22803.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___298_22803.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___298_22803.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___298_22803.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___298_22803.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___298_22803.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___298_22803.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___298_22803.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___298_22803.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___298_22803.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___298_22803.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___298_22803.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___298_22803.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___298_22803.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___298_22803.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___298_22803.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___298_22803.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___298_22803.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____22806 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___299_22814 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___299_22814.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___299_22814.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___299_22814.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___299_22814.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___299_22814.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___299_22814.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___299_22814.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___299_22814.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___299_22814.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___299_22814.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___299_22814.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___299_22814.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___299_22814.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___299_22814.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___299_22814.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___299_22814.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___299_22814.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___299_22814.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___299_22814.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___299_22814.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___299_22814.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___299_22814.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___299_22814.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___299_22814.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___299_22814.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___299_22814.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___299_22814.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___299_22814.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___299_22814.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___299_22814.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___299_22814.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___299_22814.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.dep_graph =
                                         (uu___299_22814.FStar_TypeChecker_Env.dep_graph)
                                     }) tm1 in
                                match uu____22806 with
                                | (uu____22815,uu____22816,g1) -> g1
                              else
                                (let uu____22819 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___300_22827 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___300_22827.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___300_22827.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___300_22827.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___300_22827.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___300_22827.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___300_22827.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___300_22827.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___300_22827.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___300_22827.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___300_22827.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___300_22827.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___300_22827.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___300_22827.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___300_22827.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___300_22827.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___300_22827.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___300_22827.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___300_22827.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___300_22827.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___300_22827.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___300_22827.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___300_22827.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___300_22827.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___300_22827.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___300_22827.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___300_22827.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___300_22827.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___300_22827.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___300_22827.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___300_22827.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___300_22827.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___300_22827.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___300_22827.FStar_TypeChecker_Env.dep_graph)
                                      }) tm1 in
                                 match uu____22819 with
                                 | (uu____22828,uu____22829,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___301_22832 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___301_22832.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___301_22832.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___301_22832.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____22835 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____22841  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____22835 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___302_22869 = g in
        let uu____22870 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___302_22869.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___302_22869.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___302_22869.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____22870
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
        let uu____22924 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22924 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22937 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22937
      | (reason,uu____22939,uu____22940,e,t,r)::uu____22944 ->
          let uu____22971 =
            let uu____22972 =
              let uu____22977 =
                let uu____22978 = FStar_Syntax_Print.term_to_string t in
                let uu____22979 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22978 uu____22979 in
              (uu____22977, r) in
            FStar_Errors.Error uu____22972 in
          FStar_Exn.raise uu____22971
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___303_22986 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___303_22986.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___303_22986.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___303_22986.FStar_TypeChecker_Env.implicits)
      }
let discharge_guard_nosmt:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun env  ->
    fun g  ->
      let uu____23009 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23009 with
      | FStar_Pervasives_Native.Some uu____23014 -> true
      | FStar_Pervasives_Native.None  -> false
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23024 = try_teq false env t1 t2 in
        match uu____23024 with
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
        (let uu____23044 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23044
         then
           let uu____23045 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23046 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23045
             uu____23046
         else ());
        (let uu____23048 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23048 with
         | (prob,x) ->
             let g =
               let uu____23064 =
                 let uu____23067 = singleton' env prob true in
                 solve_and_commit env uu____23067
                   (fun uu____23069  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23064 in
             ((let uu____23079 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____23079
               then
                 let uu____23080 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____23081 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____23082 =
                   let uu____23083 = FStar_Util.must g in
                   guard_to_string env uu____23083 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23080 uu____23081 uu____23082
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
        let uu____23111 = check_subtyping env t1 t2 in
        match uu____23111 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23130 =
              let uu____23131 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____23131 g in
            FStar_Pervasives_Native.Some uu____23130
let get_subtyping_prop:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23143 = check_subtyping env t1 t2 in
        match uu____23143 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23162 =
              let uu____23163 =
                let uu____23164 = FStar_Syntax_Syntax.mk_binder x in
                [uu____23164] in
              close_guard env uu____23163 g in
            FStar_Pervasives_Native.Some uu____23162
let subtype_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23175 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23175
         then
           let uu____23176 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23177 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23176
             uu____23177
         else ());
        (let uu____23179 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23179 with
         | (prob,x) ->
             let g =
               let uu____23189 =
                 let uu____23192 = singleton' env prob false in
                 solve_and_commit env uu____23192
                   (fun uu____23194  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23189 in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23205 =
                      let uu____23206 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____23206] in
                    close_guard env uu____23205 g1 in
                  discharge_guard_nosmt env g2))