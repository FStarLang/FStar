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
          let uu___112_91 = g in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___112_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___112_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___112_91.FStar_TypeChecker_Env.implicits)
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
             let uu____128 =
               let uu____129 =
                 let uu____130 =
                   let uu____133 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____133
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____130
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format2 "Guard has free variables (%s): %s" msg
                 uu____129 in
             (FStar_Errors.Fatal_FreeVariables, uu____128) in
           FStar_Errors.raise_err uu____123)
let check_term:
  Prims.string ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun msg  ->
    fun env  ->
      fun t  ->
        let s = FStar_TypeChecker_Env.unbound_vars env t in
        let uu____154 = FStar_Util.set_is_empty s in
        if uu____154
        then ()
        else
          (let uu____156 =
             let uu____161 =
               let uu____162 = FStar_Syntax_Print.term_to_string t in
               let uu____163 =
                 let uu____164 =
                   let uu____167 = FStar_Util.set_elements s in
                   FStar_All.pipe_right uu____167
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
                 FStar_All.pipe_right uu____164
                   (FStar_Syntax_Print.binders_to_string ", ") in
               FStar_Util.format3 "Term <%s> has free variables (%s): %s"
                 uu____162 msg uu____163 in
             (FStar_Errors.Fatal_FreeVariables, uu____161) in
           FStar_Errors.raise_err uu____156)
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___113_183 = g in
          let uu____184 =
            let uu____185 =
              let uu____186 =
                let uu____189 =
                  let uu____190 =
                    let uu____205 =
                      let uu____208 = FStar_Syntax_Syntax.as_arg e in
                      [uu____208] in
                    (f, uu____205) in
                  FStar_Syntax_Syntax.Tm_app uu____190 in
                FStar_Syntax_Syntax.mk uu____189 in
              uu____186 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____185 in
          {
            FStar_TypeChecker_Env.guard_f = uu____184;
            FStar_TypeChecker_Env.deferred =
              (uu___113_183.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___113_183.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___113_183.FStar_TypeChecker_Env.implicits)
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
          let uu___114_226 = g in
          let uu____227 =
            let uu____228 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____228 in
          {
            FStar_TypeChecker_Env.guard_f = uu____227;
            FStar_TypeChecker_Env.deferred =
              (uu___114_226.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___114_226.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___114_226.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____232 -> failwith "impossible"
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
          let uu____243 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____243
let check_trivial:
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____247 =
      let uu____248 = FStar_Syntax_Util.unmeta t in
      uu____248.FStar_Syntax_Syntax.n in
    match uu____247 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____252 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____283 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____283;
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
                       let uu____350 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____350
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___115_352 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___115_352.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___115_352.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___115_352.FStar_TypeChecker_Env.implicits)
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
               let uu____371 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____371
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
            let uu___116_384 = g in
            let uu____385 =
              let uu____386 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____386 in
            {
              FStar_TypeChecker_Env.guard_f = uu____385;
              FStar_TypeChecker_Env.deferred =
                (uu___116_384.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___116_384.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___116_384.FStar_TypeChecker_Env.implicits)
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
        | uu____416 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____441 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____441 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____449 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____449, uv1)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____477 = FStar_Syntax_Util.type_u () in
        match uu____477 with
        | (t_type,u) ->
            let uu____484 =
              let uu____489 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____489 t_type in
            (match uu____484 with
             | (tt,uu____491) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____524 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____564 -> false
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
    match projectee with | Failed _0 -> true | uu____766 -> false
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
    match projectee with | COVARIANT  -> true | uu____789 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____793 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____797 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___83_820  ->
    match uu___83_820 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____826 =
        let uu____827 = FStar_Syntax_Subst.compress t in
        uu____827.FStar_Syntax_Syntax.n in
      match uu____826 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____856 = FStar_Syntax_Print.uvar_to_string u in
          let uu____857 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____856 uu____857
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____860;
             FStar_Syntax_Syntax.vars = uu____861;_},args)
          ->
          let uu____907 = FStar_Syntax_Print.uvar_to_string u in
          let uu____908 = FStar_Syntax_Print.term_to_string ty in
          let uu____909 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____907 uu____908 uu____909
      | uu____910 -> "--" in
    let uu____911 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____911 detail
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___84_917  ->
      match uu___84_917 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____923 =
            let uu____926 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____927 =
              let uu____930 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____931 =
                let uu____934 =
                  let uu____937 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____937] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____934 in
              uu____930 :: uu____931 in
            uu____926 :: uu____927 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____923
      | FStar_TypeChecker_Common.CProb p ->
          let uu____943 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____944 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____945 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____943 uu____944
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____945
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___85_951  ->
      match uu___85_951 with
      | UNIV (u,t) ->
          let x =
            let uu____955 = FStar_Options.hide_uvar_nums () in
            if uu____955
            then "?"
            else
              (let uu____957 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____957 FStar_Util.string_of_int) in
          let uu____958 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____958
      | TERM ((u,uu____960),t) ->
          let x =
            let uu____967 = FStar_Options.hide_uvar_nums () in
            if uu____967
            then "?"
            else
              (let uu____969 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____969 FStar_Util.string_of_int) in
          let uu____970 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____970
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____981 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____981 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____993 =
      let uu____996 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____996
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____993 (FStar_String.concat ", ")
let args_to_string:
  'Auu____1007 .
    (FStar_Syntax_Syntax.term,'Auu____1007) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1024 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1042  ->
              match uu____1042 with
              | (x,uu____1048) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1024 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____1054 =
      let uu____1055 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1055 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1054;
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
        let uu___117_1071 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___117_1071.wl_deferred);
          ctr = (uu___117_1071.ctr);
          defer_ok = (uu___117_1071.defer_ok);
          smt_ok;
          tcenv = (uu___117_1071.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard:
  'Auu____1081 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1081,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___118_1102 = empty_worklist env in
      let uu____1103 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1103;
        wl_deferred = (uu___118_1102.wl_deferred);
        ctr = (uu___118_1102.ctr);
        defer_ok = false;
        smt_ok = (uu___118_1102.smt_ok);
        tcenv = (uu___118_1102.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___119_1117 = wl in
        {
          attempting = (uu___119_1117.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___119_1117.ctr);
          defer_ok = (uu___119_1117.defer_ok);
          smt_ok = (uu___119_1117.smt_ok);
          tcenv = (uu___119_1117.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___120_1134 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___120_1134.wl_deferred);
        ctr = (uu___120_1134.ctr);
        defer_ok = (uu___120_1134.defer_ok);
        smt_ok = (uu___120_1134.smt_ok);
        tcenv = (uu___120_1134.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1145 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1145
         then
           let uu____1146 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1146
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___86_1150  ->
    match uu___86_1150 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1154 'Auu____1155 .
    ('Auu____1155,'Auu____1154) FStar_TypeChecker_Common.problem ->
      ('Auu____1155,'Auu____1154) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___121_1172 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___121_1172.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___121_1172.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___121_1172.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___121_1172.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___121_1172.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___121_1172.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___121_1172.FStar_TypeChecker_Common.rank)
    }
let maybe_invert:
  'Auu____1180 'Auu____1181 .
    ('Auu____1181,'Auu____1180) FStar_TypeChecker_Common.problem ->
      ('Auu____1181,'Auu____1180) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___87_1201  ->
    match uu___87_1201 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___88_1225  ->
      match uu___88_1225 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___89_1228  ->
    match uu___89_1228 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___90_1241  ->
    match uu___90_1241 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___91_1256  ->
    match uu___91_1256 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___92_1271  ->
    match uu___92_1271 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___93_1288  ->
    match uu___93_1288 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___94_1305  ->
    match uu___94_1305 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___95_1318  ->
    match uu___95_1318 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1340 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1340 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1352  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem:
  'Auu____1466 'Auu____1467 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1467 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1467 ->
              'Auu____1466 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1467,'Auu____1466)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1504 = next_pid () in
                let uu____1505 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1504;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1505;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1519 'Auu____1520 .
    FStar_TypeChecker_Env.env ->
      'Auu____1520 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1520 ->
            'Auu____1519 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1520,'Auu____1519)
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
                let uu____1558 = next_pid () in
                let uu____1559 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1558;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1559;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1572 'Auu____1573 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1573 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1573 ->
            'Auu____1572 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1573,'Auu____1572) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1606 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1606;
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
  'Auu____1612 .
    worklist ->
      ('Auu____1612,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1662 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1662
        then
          let uu____1663 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1664 = prob_to_string env d in
          let uu____1665 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1663 uu____1664 uu____1665 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1671 -> failwith "impossible" in
           let uu____1672 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1686 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1687 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1686, uu____1687)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1693 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1694 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1693, uu____1694) in
           match uu____1672 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___96_1710  ->
            match uu___96_1710 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1722 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1724),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___97_1744  ->
           match uu___97_1744 with
           | UNIV uu____1747 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1753),t) ->
               let uu____1759 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1759
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
        (fun uu___98_1779  ->
           match uu___98_1779 with
           | UNIV (u',t) ->
               let uu____1784 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1784
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1788 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1795 =
        let uu____1796 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1796 in
      FStar_Syntax_Subst.compress uu____1795
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1803 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1803
let norm_arg:
  'Auu____1807 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1807) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1807)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1828 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1828, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1859  ->
              match uu____1859 with
              | (x,imp) ->
                  let uu____1870 =
                    let uu___122_1871 = x in
                    let uu____1872 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___122_1871.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___122_1871.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1872
                    } in
                  (uu____1870, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1887 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1887
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1891 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1891
        | uu____1894 -> u2 in
      let uu____1895 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1895
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
                (let uu____2007 = norm_refinement env t12 in
                 match uu____2007 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2024;
                     FStar_Syntax_Syntax.vars = uu____2025;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2051 =
                       let uu____2052 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2053 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2052 uu____2053 in
                     failwith uu____2051)
          | FStar_Syntax_Syntax.Tm_uinst uu____2068 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2105 =
                   let uu____2106 = FStar_Syntax_Subst.compress t1' in
                   uu____2106.FStar_Syntax_Syntax.n in
                 match uu____2105 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2123 -> aux true t1'
                 | uu____2130 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2145 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2176 =
                   let uu____2177 = FStar_Syntax_Subst.compress t1' in
                   uu____2177.FStar_Syntax_Syntax.n in
                 match uu____2176 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2194 -> aux true t1'
                 | uu____2201 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2216 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2261 =
                   let uu____2262 = FStar_Syntax_Subst.compress t1' in
                   uu____2262.FStar_Syntax_Syntax.n in
                 match uu____2261 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2279 -> aux true t1'
                 | uu____2286 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2301 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2316 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2331 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2346 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2361 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2388 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2419 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2450 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2477 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2514 ->
              let uu____2521 =
                let uu____2522 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2523 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2522 uu____2523 in
              failwith uu____2521
          | FStar_Syntax_Syntax.Tm_ascribed uu____2538 ->
              let uu____2565 =
                let uu____2566 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2567 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2566 uu____2567 in
              failwith uu____2565
          | FStar_Syntax_Syntax.Tm_delayed uu____2582 ->
              let uu____2607 =
                let uu____2608 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2609 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2608 uu____2609 in
              failwith uu____2607
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2624 =
                let uu____2625 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2626 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2625 uu____2626 in
              failwith uu____2624 in
        let uu____2641 = whnf env t1 in aux false uu____2641
let base_and_refinement:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t
let normalize_refinement:
  'Auu____2663 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2663 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2686 = base_and_refinement env t in
      FStar_All.pipe_right uu____2686 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2720 = FStar_Syntax_Syntax.null_bv t in
    (uu____2720, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2726 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2726 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2747 = base_and_refinement_maybe_delta delta1 env t in
          match uu____2747 with
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
  fun uu____2826  ->
    match uu____2826 with
    | (t_base,refopt) ->
        let uu____2853 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2853 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2885 =
      let uu____2888 =
        let uu____2891 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2914  ->
                  match uu____2914 with | (uu____2921,uu____2922,x) -> x)) in
        FStar_List.append wl.attempting uu____2891 in
      FStar_List.map (wl_prob_to_string wl) uu____2888 in
    FStar_All.pipe_right uu____2885 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2935 =
          let uu____2948 =
            let uu____2949 = FStar_Syntax_Subst.compress k in
            uu____2949.FStar_Syntax_Syntax.n in
          match uu____2948 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3002 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3002)
              else
                (let uu____3016 = FStar_Syntax_Util.abs_formals t in
                 match uu____3016 with
                 | (ys',t1,uu____3039) ->
                     let uu____3044 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3044))
          | uu____3085 ->
              let uu____3086 =
                let uu____3097 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3097) in
              ((ys, t), uu____3086) in
        match uu____2935 with
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
                 let uu____3146 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3146 c in
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
            let uu____3174 = p_guard prob in
            match uu____3174 with
            | (uu____3179,uv) ->
                ((let uu____3182 =
                    let uu____3183 = FStar_Syntax_Subst.compress uv in
                    uu____3183.FStar_Syntax_Syntax.n in
                  match uu____3182 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3215 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3215
                        then
                          let uu____3216 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3217 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3218 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3216
                            uu____3217 uu____3218
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3220 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___123_3223 = wl in
                  {
                    attempting = (uu___123_3223.attempting);
                    wl_deferred = (uu___123_3223.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___123_3223.defer_ok);
                    smt_ok = (uu___123_3223.smt_ok);
                    tcenv = (uu___123_3223.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3238 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3238
         then
           let uu____3239 = FStar_Util.string_of_int pid in
           let uu____3240 =
             let uu____3241 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3241 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3239 uu____3240
         else ());
        commit sol;
        (let uu___124_3248 = wl in
         {
           attempting = (uu___124_3248.attempting);
           wl_deferred = (uu___124_3248.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___124_3248.defer_ok);
           smt_ok = (uu___124_3248.smt_ok);
           tcenv = (uu___124_3248.tcenv)
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
            | (uu____3286,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3298 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3298 in
          (let uu____3304 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3304
           then
             let uu____3305 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3306 =
               let uu____3307 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3307 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3305 uu____3306
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
        let uu____3339 =
          let uu____3346 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3346 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3339
          (FStar_Util.for_some
             (fun uu____3382  ->
                match uu____3382 with
                | (uv,uu____3388) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3395 'Auu____3396 .
    'Auu____3396 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3395)
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
            let uu____3428 = occurs wl uk t in Prims.op_Negation uu____3428 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3435 =
                 let uu____3436 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3437 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3436 uu____3437 in
               FStar_Pervasives_Native.Some uu____3435) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3447 'Auu____3448 .
    'Auu____3448 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3447)
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
            let uu____3502 = occurs_check env wl uk t in
            match uu____3502 with
            | (occurs_ok,msg) ->
                let uu____3533 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3533, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3556 'Auu____3557 .
    (FStar_Syntax_Syntax.bv,'Auu____3557) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3556) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3556) FStar_Pervasives_Native.tuple2
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
      let uu____3641 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3695  ->
                fun uu____3696  ->
                  match (uu____3695, uu____3696) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3777 =
                        let uu____3778 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3778 in
                      if uu____3777
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3803 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3803
                         then
                           let uu____3816 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3816)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3641 with | (isect,uu____3857) -> FStar_List.rev isect
let binders_eq:
  'Auu____3882 'Auu____3883 .
    (FStar_Syntax_Syntax.bv,'Auu____3883) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3882) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3938  ->
              fun uu____3939  ->
                match (uu____3938, uu____3939) with
                | ((a,uu____3957),(b,uu____3959)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3973 'Auu____3974 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3974) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3973)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3973)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4025 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4039  ->
                      match uu____4039 with
                      | (b,uu____4045) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4025
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4061 -> FStar_Pervasives_Native.None
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
            let uu____4134 = pat_var_opt env seen hd1 in
            (match uu____4134 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4148 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4148
                   then
                     let uu____4149 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4149
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4167 =
      let uu____4168 = FStar_Syntax_Subst.compress t in
      uu____4168.FStar_Syntax_Syntax.n in
    match uu____4167 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4171 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4188;
           FStar_Syntax_Syntax.pos = uu____4189;
           FStar_Syntax_Syntax.vars = uu____4190;_},uu____4191)
        -> true
    | uu____4228 -> false
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
           FStar_Syntax_Syntax.pos = uu____4352;
           FStar_Syntax_Syntax.vars = uu____4353;_},args)
        -> (t, uv, k, args)
    | uu____4421 -> failwith "Not a flex-uvar"
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
      let uu____4498 = destruct_flex_t t in
      match uu____4498 with
      | (t1,uv,k,args) ->
          let uu____4613 = pat_vars env [] args in
          (match uu____4613 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4711 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4792 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4827 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4831 -> false
let head_match: match_result -> match_result =
  fun uu___99_4834  ->
    match uu___99_4834 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4849 -> HeadMatch
let and_match: match_result -> (Prims.unit -> match_result) -> match_result =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch i -> MisMatch i
      | HeadMatch  ->
          let uu____4870 = m2 () in
          (match uu____4870 with
           | MisMatch j -> MisMatch j
           | uu____4880 -> HeadMatch)
      | FullMatch  -> m2 ()
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4889 ->
          let uu____4890 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4890 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4901 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4920 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4929 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4956 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4957 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4958 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4975 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4988 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5012) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5018,uu____5019) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5061) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5082;
             FStar_Syntax_Syntax.index = uu____5083;
             FStar_Syntax_Syntax.sort = t2;_},uu____5085)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5092 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5093 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5094 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5107 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5125 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5125
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
            let uu____5152 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5152
            then FullMatch
            else
              (let uu____5154 =
                 let uu____5163 =
                   let uu____5166 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5166 in
                 let uu____5167 =
                   let uu____5170 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5170 in
                 (uu____5163, uu____5167) in
               MisMatch uu____5154)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5176),FStar_Syntax_Syntax.Tm_uinst (g,uu____5178)) ->
            let uu____5187 = head_matches env f g in
            FStar_All.pipe_right uu____5187 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5190 = FStar_Const.eq_const c d in
            if uu____5190
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5197),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5199)) ->
            let uu____5248 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5248
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5255),FStar_Syntax_Syntax.Tm_refine (y,uu____5257)) ->
            let uu____5266 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5266 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5268),uu____5269) ->
            let uu____5274 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5274 head_match
        | (uu____5275,FStar_Syntax_Syntax.Tm_refine (x,uu____5277)) ->
            let uu____5282 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5282 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5283,FStar_Syntax_Syntax.Tm_type
           uu____5284) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5285,FStar_Syntax_Syntax.Tm_arrow uu____5286) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            if (FStar_List.length bs1) = (FStar_List.length bs2)
            then
              let uu____5415 =
                let uu____5416 = FStar_List.zip bs1 bs2 in
                let uu____5451 = head_matches env t12 t22 in
                FStar_List.fold_right
                  (fun uu____5460  ->
                     fun a  ->
                       match uu____5460 with
                       | (b1,b2) ->
                           and_match a
                             (fun uu____5469  -> branch_matches env b1 b2))
                  uu____5416 uu____5451 in
              FStar_All.pipe_right uu____5415 head_match
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5476),FStar_Syntax_Syntax.Tm_app (head',uu____5478))
            ->
            let uu____5519 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5519 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5521),uu____5522) ->
            let uu____5543 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5543 head_match
        | (uu____5544,FStar_Syntax_Syntax.Tm_app (head1,uu____5546)) ->
            let uu____5567 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5567 head_match
        | uu____5568 ->
            let uu____5573 =
              let uu____5582 = delta_depth_of_term env t11 in
              let uu____5585 = delta_depth_of_term env t21 in
              (uu____5582, uu____5585) in
            MisMatch uu____5573
and branch_matches:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch -> match_result
  =
  fun env  ->
    fun b1  ->
      fun b2  ->
        let related_by f o1 o2 =
          match (o1, o2) with
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
              true
          | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y)
              -> f x y
          | (uu____5637,uu____5638) -> false in
        let uu____5647 = b1 in
        match uu____5647 with
        | (p1,w1,t1) ->
            let uu____5667 = b2 in
            (match uu____5667 with
             | (p2,w2,t2) ->
                 let uu____5687 = FStar_Syntax_Syntax.eq_pat p1 p2 in
                 if uu____5687
                 then
                   let uu____5688 =
                     (let uu____5691 = FStar_Syntax_Util.eq_tm t1 t2 in
                      uu____5691 = FStar_Syntax_Util.Equal) &&
                       (related_by
                          (fun t11  ->
                             fun t21  ->
                               let uu____5700 =
                                 FStar_Syntax_Util.eq_tm t11 t21 in
                               uu____5700 = FStar_Syntax_Util.Equal) w1 w2) in
                   (if uu____5688
                    then FullMatch
                    else
                      MisMatch
                        (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.None))
                 else
                   MisMatch
                     (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None))
let head_matches_delta:
  'Auu____5716 .
    FStar_TypeChecker_Env.env ->
      'Auu____5716 ->
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
            let uu____5749 = FStar_Syntax_Util.head_and_args t in
            match uu____5749 with
            | (head1,uu____5767) ->
                let uu____5788 =
                  let uu____5789 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5789.FStar_Syntax_Syntax.n in
                (match uu____5788 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5795 =
                       let uu____5796 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5796 FStar_Option.isSome in
                     if uu____5795
                     then
                       let uu____5815 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5815
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5819 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5922)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5940 =
                     let uu____5949 = maybe_inline t11 in
                     let uu____5952 = maybe_inline t21 in
                     (uu____5949, uu____5952) in
                   match uu____5940 with
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
                (uu____5989,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____6007 =
                     let uu____6016 = maybe_inline t11 in
                     let uu____6019 = maybe_inline t21 in
                     (uu____6016, uu____6019) in
                   match uu____6007 with
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
                let uu____6062 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____6062 with
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
                let uu____6085 =
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
                (match uu____6085 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6109 -> fail r
            | uu____6118 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6151 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6187 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___100_6199  ->
    match uu___100_6199 with
    | T (t,uu____6201) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6217 = FStar_Syntax_Util.type_u () in
      match uu____6217 with
      | (t,uu____6223) ->
          let uu____6224 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6224
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
        let uu____6299 = head_matches env t1 t' in
        match uu____6299 with
        | MisMatch uu____6300 -> false
        | uu____6309 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6405,imp),T (t2,uu____6408)) -> (t2, imp)
                     | uu____6427 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6494  ->
                    match uu____6494 with
                    | (t2,uu____6508) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6551 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6551 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6626))::tcs2) ->
                       aux
                         (((let uu___125_6661 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_6661.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_6661.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6679 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___101_6732 =
                 match uu___101_6732 with
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
               let uu____6849 = decompose1 [] bs1 in
               (rebuild, matches, uu____6849))
      | uu____6898 ->
          let rebuild uu___102_6904 =
            match uu___102_6904 with
            | [] -> t1
            | uu____6907 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___103_6938  ->
    match uu___103_6938 with
    | T (t,uu____6940) -> t
    | uu____6949 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___104_6952  ->
    match uu___104_6952 with
    | T (t,uu____6954) -> FStar_Syntax_Syntax.as_arg t
    | uu____6963 -> failwith "Impossible"
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
              | (uu____7069,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7094 = new_uvar r scope1 k in
                  (match uu____7094 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7112 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7129 =
                         let uu____7130 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7130 in
                       ((T (gi_xs, mk_kind)), uu____7129))
              | (uu____7143,uu____7144,C uu____7145) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7292 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7309;
                         FStar_Syntax_Syntax.vars = uu____7310;_})
                        ->
                        let uu____7333 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7333 with
                         | (T (gi_xs,uu____7357),prob) ->
                             let uu____7367 =
                               let uu____7368 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7368 in
                             (uu____7367, [prob])
                         | uu____7371 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7386;
                         FStar_Syntax_Syntax.vars = uu____7387;_})
                        ->
                        let uu____7410 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7410 with
                         | (T (gi_xs,uu____7434),prob) ->
                             let uu____7444 =
                               let uu____7445 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7445 in
                             (uu____7444, [prob])
                         | uu____7448 -> failwith "impossible")
                    | (uu____7459,uu____7460,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7462;
                         FStar_Syntax_Syntax.vars = uu____7463;_})
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
                        let uu____7594 =
                          let uu____7603 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7603 FStar_List.unzip in
                        (match uu____7594 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7657 =
                                 let uu____7658 =
                                   let uu____7661 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7661 un_T in
                                 let uu____7662 =
                                   let uu____7671 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7671
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7658;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7662;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7657 in
                             ((C gi_xs), sub_probs))
                    | uu____7680 ->
                        let uu____7693 = sub_prob scope1 args q in
                        (match uu____7693 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7292 with
                   | (tc,probs) ->
                       let uu____7724 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7787,uu____7788),T
                            (t,uu____7790)) ->
                             let b1 =
                               ((let uu___126_7827 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___126_7827.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___126_7827.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7828 =
                               let uu____7835 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7835 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7828)
                         | uu____7870 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7724 with
                        | (bopt,scope2,args1) ->
                            let uu____7954 = aux scope2 args1 qs2 in
                            (match uu____7954 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7991 =
                                         let uu____7994 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7994 in
                                       FStar_Syntax_Util.mk_conj_l uu____7991
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____8017 =
                                         let uu____8020 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____8021 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____8020 :: uu____8021 in
                                       FStar_Syntax_Util.mk_conj_l uu____8017 in
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
  'Auu____8089 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8089)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8089)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___127_8110 = p in
      let uu____8115 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8116 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___127_8110.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8115;
        FStar_TypeChecker_Common.relation =
          (uu___127_8110.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8116;
        FStar_TypeChecker_Common.element =
          (uu___127_8110.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___127_8110.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___127_8110.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___127_8110.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___127_8110.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___127_8110.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8128 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8128
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8137 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8157 = compress_prob wl pr in
        FStar_All.pipe_right uu____8157 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8167 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8167 with
           | (lh,uu____8187) ->
               let uu____8208 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8208 with
                | (rh,uu____8228) ->
                    let uu____8249 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8266,FStar_Syntax_Syntax.Tm_uvar uu____8267)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8304,uu____8305)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8326,FStar_Syntax_Syntax.Tm_uvar uu____8327)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8348,uu____8349)
                          ->
                          let uu____8366 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8366 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8415 ->
                                    let rank =
                                      let uu____8423 = is_top_level_prob prob in
                                      if uu____8423
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8425 =
                                      let uu___128_8430 = tp in
                                      let uu____8435 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___128_8430.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___128_8430.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___128_8430.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8435;
                                        FStar_TypeChecker_Common.element =
                                          (uu___128_8430.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___128_8430.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___128_8430.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___128_8430.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___128_8430.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___128_8430.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8425)))
                      | (uu____8446,FStar_Syntax_Syntax.Tm_uvar uu____8447)
                          ->
                          let uu____8464 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8464 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8513 ->
                                    let uu____8520 =
                                      let uu___129_8527 = tp in
                                      let uu____8532 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___129_8527.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8532;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___129_8527.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___129_8527.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___129_8527.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___129_8527.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___129_8527.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___129_8527.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___129_8527.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___129_8527.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8520)))
                      | (uu____8549,uu____8550) -> (rigid_rigid, tp) in
                    (match uu____8249 with
                     | (rank,tp1) ->
                         let uu____8569 =
                           FStar_All.pipe_right
                             (let uu___130_8575 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___130_8575.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___130_8575.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___130_8575.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___130_8575.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___130_8575.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___130_8575.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___130_8575.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___130_8575.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___130_8575.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8569))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8585 =
            FStar_All.pipe_right
              (let uu___131_8591 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___131_8591.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___131_8591.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___131_8591.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___131_8591.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___131_8591.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___131_8591.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___131_8591.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___131_8591.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___131_8591.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8585)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8646 probs =
      match uu____8646 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8699 = rank wl hd1 in
               (match uu____8699 with
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
    match projectee with | UDeferred _0 -> true | uu____8806 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8818 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8830 -> false
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
                        let uu____8870 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8870 with
                        | (k,uu____8876) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8886 -> false)))
            | uu____8887 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8938 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8938 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8941 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8951 =
                     let uu____8952 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8953 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8952
                       uu____8953 in
                   UFailed uu____8951)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8973 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8973 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8995 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8995 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8998 ->
                let uu____9003 =
                  let uu____9004 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____9005 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9004
                    uu____9005 msg in
                UFailed uu____9003 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9006,uu____9007) ->
              let uu____9008 =
                let uu____9009 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9010 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9009 uu____9010 in
              failwith uu____9008
          | (FStar_Syntax_Syntax.U_unknown ,uu____9011) ->
              let uu____9012 =
                let uu____9013 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9014 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9013 uu____9014 in
              failwith uu____9012
          | (uu____9015,FStar_Syntax_Syntax.U_bvar uu____9016) ->
              let uu____9017 =
                let uu____9018 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9019 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9018 uu____9019 in
              failwith uu____9017
          | (uu____9020,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9021 =
                let uu____9022 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9023 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9022 uu____9023 in
              failwith uu____9021
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9047 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9047
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9069 = occurs_univ v1 u3 in
              if uu____9069
              then
                let uu____9070 =
                  let uu____9071 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9072 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9071 uu____9072 in
                try_umax_components u11 u21 uu____9070
              else
                (let uu____9074 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9074)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9094 = occurs_univ v1 u3 in
              if uu____9094
              then
                let uu____9095 =
                  let uu____9096 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9097 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9096 uu____9097 in
                try_umax_components u11 u21 uu____9095
              else
                (let uu____9099 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9099)
          | (FStar_Syntax_Syntax.U_max uu____9108,uu____9109) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9115 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9115
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9117,FStar_Syntax_Syntax.U_max uu____9118) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9124 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9124
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9126,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9127,FStar_Syntax_Syntax.U_name
             uu____9128) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9129) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9130) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9131,FStar_Syntax_Syntax.U_succ
             uu____9132) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9133,FStar_Syntax_Syntax.U_zero
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
      let uu____9219 = bc1 in
      match uu____9219 with
      | (bs1,mk_cod1) ->
          let uu____9260 = bc2 in
          (match uu____9260 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9330 = FStar_Util.first_N n1 bs in
                 match uu____9330 with
                 | (bs3,rest) ->
                     let uu____9355 = mk_cod rest in (bs3, uu____9355) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9384 =
                   let uu____9391 = mk_cod1 [] in (bs1, uu____9391) in
                 let uu____9394 =
                   let uu____9401 = mk_cod2 [] in (bs2, uu____9401) in
                 (uu____9384, uu____9394)
               else
                 if l1 > l2
                 then
                   (let uu____9443 = curry l2 bs1 mk_cod1 in
                    let uu____9456 =
                      let uu____9463 = mk_cod2 [] in (bs2, uu____9463) in
                    (uu____9443, uu____9456))
                 else
                   (let uu____9479 =
                      let uu____9486 = mk_cod1 [] in (bs1, uu____9486) in
                    let uu____9489 = curry l1 bs2 mk_cod2 in
                    (uu____9479, uu____9489)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9610 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9610
       then
         let uu____9611 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9611
       else ());
      (let uu____9613 = next_prob probs in
       match uu____9613 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___132_9634 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___132_9634.wl_deferred);
               ctr = (uu___132_9634.ctr);
               defer_ok = (uu___132_9634.defer_ok);
               smt_ok = (uu___132_9634.smt_ok);
               tcenv = (uu___132_9634.tcenv)
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
                  let uu____9645 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9645 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9650 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9650 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9655,uu____9656) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9673 ->
                let uu____9682 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9741  ->
                          match uu____9741 with
                          | (c,uu____9749,uu____9750) -> c < probs.ctr)) in
                (match uu____9682 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9791 =
                            FStar_List.map
                              (fun uu____9806  ->
                                 match uu____9806 with
                                 | (uu____9817,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9791
                      | uu____9820 ->
                          let uu____9829 =
                            let uu___133_9830 = probs in
                            let uu____9831 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9852  ->
                                      match uu____9852 with
                                      | (uu____9859,uu____9860,y) -> y)) in
                            {
                              attempting = uu____9831;
                              wl_deferred = rest;
                              ctr = (uu___133_9830.ctr);
                              defer_ok = (uu___133_9830.defer_ok);
                              smt_ok = (uu___133_9830.smt_ok);
                              tcenv = (uu___133_9830.tcenv)
                            } in
                          solve env uu____9829))))
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
            let uu____9867 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9867 with
            | USolved wl1 ->
                let uu____9869 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9869
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
                  let uu____9915 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9915 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9918 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9930;
                  FStar_Syntax_Syntax.vars = uu____9931;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9934;
                  FStar_Syntax_Syntax.vars = uu____9935;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9949,uu____9950) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9957,FStar_Syntax_Syntax.Tm_uinst uu____9958) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9965 -> USolved wl
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
            ((let uu____9975 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9975
              then
                let uu____9976 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9976 msg
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
        (let uu____9985 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9985
         then
           let uu____9986 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9986
         else ());
        (let uu____9988 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9988 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10050 = head_matches_delta env () t1 t2 in
               match uu____10050 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10091 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10140 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10155 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10156 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10155, uu____10156)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10161 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10162 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10161, uu____10162) in
                        (match uu____10140 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10188 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10188 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10219 =
                                    let uu____10228 =
                                      let uu____10231 =
                                        let uu____10234 =
                                          let uu____10235 =
                                            let uu____10242 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10242) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10235 in
                                        FStar_Syntax_Syntax.mk uu____10234 in
                                      uu____10231
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10250 =
                                      let uu____10253 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10253] in
                                    (uu____10228, uu____10250) in
                                  FStar_Pervasives_Native.Some uu____10219
                              | (uu____10266,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10268)) ->
                                  let uu____10273 =
                                    let uu____10280 =
                                      let uu____10283 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10283] in
                                    (t11, uu____10280) in
                                  FStar_Pervasives_Native.Some uu____10273
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10293),uu____10294) ->
                                  let uu____10299 =
                                    let uu____10306 =
                                      let uu____10309 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10309] in
                                    (t21, uu____10306) in
                                  FStar_Pervasives_Native.Some uu____10299
                              | uu____10318 ->
                                  let uu____10323 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10323 with
                                   | (head1,uu____10347) ->
                                       let uu____10368 =
                                         let uu____10369 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10369.FStar_Syntax_Syntax.n in
                                       (match uu____10368 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10380;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10382;_}
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
                                        | uu____10389 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10402) ->
                  let uu____10427 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___105_10453  ->
                            match uu___105_10453 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10460 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10460 with
                                      | (u',uu____10476) ->
                                          let uu____10497 =
                                            let uu____10498 = whnf env u' in
                                            uu____10498.FStar_Syntax_Syntax.n in
                                          (match uu____10497 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10502) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10527 -> false))
                                 | uu____10528 -> false)
                            | uu____10531 -> false)) in
                  (match uu____10427 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10565 tps =
                         match uu____10565 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10613 =
                                    let uu____10622 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10622 in
                                  (match uu____10613 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10657 -> FStar_Pervasives_Native.None) in
                       let uu____10666 =
                         let uu____10675 =
                           let uu____10682 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10682, []) in
                         make_lower_bound uu____10675 lower_bounds in
                       (match uu____10666 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10694 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10694
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
                            ((let uu____10714 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10714
                              then
                                let wl' =
                                  let uu___134_10716 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___134_10716.wl_deferred);
                                    ctr = (uu___134_10716.ctr);
                                    defer_ok = (uu___134_10716.defer_ok);
                                    smt_ok = (uu___134_10716.smt_ok);
                                    tcenv = (uu___134_10716.tcenv)
                                  } in
                                let uu____10717 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10717
                              else ());
                             (let uu____10719 =
                                solve_t env eq_prob
                                  (let uu___135_10721 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___135_10721.wl_deferred);
                                     ctr = (uu___135_10721.ctr);
                                     defer_ok = (uu___135_10721.defer_ok);
                                     smt_ok = (uu___135_10721.smt_ok);
                                     tcenv = (uu___135_10721.tcenv)
                                   }) in
                              match uu____10719 with
                              | Success uu____10724 ->
                                  let wl1 =
                                    let uu___136_10726 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___136_10726.wl_deferred);
                                      ctr = (uu___136_10726.ctr);
                                      defer_ok = (uu___136_10726.defer_ok);
                                      smt_ok = (uu___136_10726.smt_ok);
                                      tcenv = (uu___136_10726.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10728 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10733 -> FStar_Pervasives_Native.None))))
              | uu____10734 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10743 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10743
         then
           let uu____10744 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10744
         else ());
        (let uu____10746 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10746 with
         | (u,args) ->
             let uu____10785 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10785 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10826 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10826 with
                    | (h1,args1) ->
                        let uu____10867 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10867 with
                         | (h2,uu____10887) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10914 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10914
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10932 =
                                          let uu____10935 =
                                            let uu____10936 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10936 in
                                          [uu____10935] in
                                        FStar_Pervasives_Native.Some
                                          uu____10932))
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
                                       (let uu____10969 =
                                          let uu____10972 =
                                            let uu____10973 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10973 in
                                          [uu____10972] in
                                        FStar_Pervasives_Native.Some
                                          uu____10969))
                                  else FStar_Pervasives_Native.None
                              | uu____10987 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11077 =
                               let uu____11086 =
                                 let uu____11089 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11089 in
                               (uu____11086, m1) in
                             FStar_Pervasives_Native.Some uu____11077)
                    | (uu____11102,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11104)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11152),uu____11153) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11200 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11253) ->
                       let uu____11278 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___106_11304  ->
                                 match uu___106_11304 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11311 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11311 with
                                           | (u',uu____11327) ->
                                               let uu____11348 =
                                                 let uu____11349 =
                                                   whnf env u' in
                                                 uu____11349.FStar_Syntax_Syntax.n in
                                               (match uu____11348 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11353) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11378 -> false))
                                      | uu____11379 -> false)
                                 | uu____11382 -> false)) in
                       (match uu____11278 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11420 tps =
                              match uu____11420 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11482 =
                                         let uu____11493 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11493 in
                                       (match uu____11482 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11544 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11555 =
                              let uu____11566 =
                                let uu____11575 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11575, []) in
                              make_upper_bound uu____11566 upper_bounds in
                            (match uu____11555 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11589 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11589
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
                                 ((let uu____11615 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11615
                                   then
                                     let wl' =
                                       let uu___137_11617 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___137_11617.wl_deferred);
                                         ctr = (uu___137_11617.ctr);
                                         defer_ok = (uu___137_11617.defer_ok);
                                         smt_ok = (uu___137_11617.smt_ok);
                                         tcenv = (uu___137_11617.tcenv)
                                       } in
                                     let uu____11618 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11618
                                   else ());
                                  (let uu____11620 =
                                     solve_t env eq_prob
                                       (let uu___138_11622 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___138_11622.wl_deferred);
                                          ctr = (uu___138_11622.ctr);
                                          defer_ok =
                                            (uu___138_11622.defer_ok);
                                          smt_ok = (uu___138_11622.smt_ok);
                                          tcenv = (uu___138_11622.tcenv)
                                        }) in
                                   match uu____11620 with
                                   | Success uu____11625 ->
                                       let wl1 =
                                         let uu___139_11627 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___139_11627.wl_deferred);
                                           ctr = (uu___139_11627.ctr);
                                           defer_ok =
                                             (uu___139_11627.defer_ok);
                                           smt_ok = (uu___139_11627.smt_ok);
                                           tcenv = (uu___139_11627.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11629 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11634 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11635 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11710 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11710
                      then
                        let uu____11711 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11711
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___140_11765 = hd1 in
                      let uu____11766 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___140_11765.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___140_11765.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11766
                      } in
                    let hd21 =
                      let uu___141_11770 = hd2 in
                      let uu____11771 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___141_11770.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___141_11770.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11771
                      } in
                    let prob =
                      let uu____11775 =
                        let uu____11780 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11780 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11775 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11791 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11791 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11795 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11795 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11833 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11838 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11833 uu____11838 in
                         ((let uu____11848 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11848
                           then
                             let uu____11849 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11850 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11849 uu____11850
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11873 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11883 = aux scope env [] bs1 bs2 in
              match uu____11883 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11907 = compress_tprob wl problem in
        solve_t' env uu____11907 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11940 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11940 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11971,uu____11972) ->
                   let rec may_relate head3 =
                     let uu____11997 =
                       let uu____11998 = FStar_Syntax_Subst.compress head3 in
                       uu____11998.FStar_Syntax_Syntax.n in
                     match uu____11997 with
                     | FStar_Syntax_Syntax.Tm_name uu____12001 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12002 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12025;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12026;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12029;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12030;
                           FStar_Syntax_Syntax.fv_qual = uu____12031;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12035,uu____12036) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12078) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12084) ->
                         may_relate t
                     | uu____12089 -> false in
                   let uu____12090 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12090
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
                                let uu____12107 =
                                  let uu____12108 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12108 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12107 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12110 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12110
                   else
                     (let uu____12112 =
                        let uu____12113 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12114 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12113 uu____12114 in
                      giveup env1 uu____12112 orig)
               | (uu____12115,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___142_12129 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___142_12129.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___142_12129.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___142_12129.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___142_12129.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___142_12129.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___142_12129.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___142_12129.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___142_12129.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12130,FStar_Pervasives_Native.None ) ->
                   ((let uu____12142 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12142
                     then
                       let uu____12143 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12144 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12145 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12146 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12143
                         uu____12144 uu____12145 uu____12146
                     else ());
                    (let uu____12148 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12148 with
                     | (head11,args1) ->
                         let uu____12185 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12185 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12239 =
                                  let uu____12240 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12241 = args_to_string args1 in
                                  let uu____12242 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12243 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12240 uu____12241 uu____12242
                                    uu____12243 in
                                giveup env1 uu____12239 orig
                              else
                                (let uu____12245 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12251 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12251 = FStar_Syntax_Util.Equal) in
                                 if uu____12245
                                 then
                                   let uu____12252 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12252 with
                                   | USolved wl2 ->
                                       let uu____12254 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12254
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12258 =
                                      base_and_refinement env1 t1 in
                                    match uu____12258 with
                                    | (base1,refinement1) ->
                                        let uu____12283 =
                                          base_and_refinement env1 t2 in
                                        (match uu____12283 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12340 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12340 with
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
                                                           (fun uu____12362 
                                                              ->
                                                              fun uu____12363
                                                                 ->
                                                                match 
                                                                  (uu____12362,
                                                                    uu____12363)
                                                                with
                                                                | ((a,uu____12381),
                                                                   (a',uu____12383))
                                                                    ->
                                                                    let uu____12392
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
                                                                    uu____12392)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12402 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12402 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12408 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___143_12444 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___143_12444.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12477 =
          match uu____12477 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12519 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu____12519 then f () else () in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12615  ->
                     let uu____12616 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12616);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12684  ->
                               match uu____12684 with
                               | (x,imp) ->
                                   let uu____12695 =
                                     FStar_Syntax_Syntax.bv_to_name x in
                                   (uu____12695, imp))) in
                     let pattern_vars1 = FStar_List.rev pattern_vars in
                     let kk =
                       let uu____12708 = FStar_Syntax_Util.type_u () in
                       match uu____12708 with
                       | (t1,uu____12714) ->
                           let uu____12715 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1 in
                           FStar_Pervasives_Native.fst uu____12715 in
                     let uu____12720 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                     (match uu____12720 with
                      | (t',tm_u1) ->
                          let uu____12733 = destruct_flex_t t' in
                          (match uu____12733 with
                           | (uu____12770,u1,k1,uu____12773) ->
                               let all_formals = FStar_List.rev seen_formals in
                               let k2 =
                                 let uu____12832 =
                                   FStar_Syntax_Syntax.mk_Total res_t in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____12832 in
                               let sol =
                                 let uu____12836 =
                                   let uu____12845 = u_abs k2 all_formals t' in
                                   ((u, k2), uu____12845) in
                                 TERM uu____12836 in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____12980  ->
                           let uu____12981 =
                             FStar_Syntax_Print.binder_to_string formal in
                           let uu____12982 =
                             FStar_Syntax_Print.args_to_string [hd1] in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____12981 uu____12982);
                      (let uu____12995 = pat_var_opt env pat_args hd1 in
                       match uu____12995 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____13015  ->
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
                                      (fun uu____13058  ->
                                         match uu____13058 with
                                         | (x,uu____13064) ->
                                             FStar_Syntax_Syntax.bv_eq x
                                               (FStar_Pervasives_Native.fst y))) in
                           if Prims.op_Negation maybe_pat
                           then
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1
                           else
                             (debug1
                                (fun uu____13079  ->
                                   let uu____13080 =
                                     FStar_Syntax_Print.args_to_string [hd1] in
                                   let uu____13093 =
                                     FStar_Syntax_Print.binder_to_string y in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____13080
                                     uu____13093);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                               let uu____13097 =
                                 let uu____13098 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set in
                                 Prims.op_Negation uu____13098 in
                               if uu____13097
                               then
                                 (debug1
                                    (fun uu____13110  ->
                                       let uu____13111 =
                                         let uu____13114 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1] in
                                         let uu____13127 =
                                           let uu____13130 =
                                             FStar_Syntax_Print.binder_to_string
                                               y in
                                           let uu____13131 =
                                             let uu____13134 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort in
                                             let uu____13135 =
                                               let uu____13138 =
                                                 names_to_string fvs in
                                               let uu____13139 =
                                                 let uu____13142 =
                                                   names_to_string
                                                     pattern_var_set in
                                                 [uu____13142] in
                                               uu____13138 :: uu____13139 in
                                             uu____13134 :: uu____13135 in
                                           uu____13130 :: uu____13131 in
                                         uu____13114 :: uu____13127 in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____13111);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____13144 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set in
                                  let uu____13147 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set in
                                  aux (y :: pat_args) uu____13144 (formal ::
                                    pattern_vars) uu____13147 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____13154::uu____13155) ->
                     let uu____13186 =
                       let uu____13199 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                       FStar_Syntax_Util.arrow_formals uu____13199 in
                     (match uu____13186 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____13238 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____13245::uu____13246,[]) ->
                     FStar_Pervasives_Native.None) in
              let uu____13269 =
                let uu____13282 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13282 in
              (match uu____13269 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____13318  ->
                         let uu____13319 =
                           FStar_Syntax_Print.term_to_string t in
                         let uu____13320 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals in
                         let uu____13321 =
                           FStar_Syntax_Print.term_to_string res_t in
                         let uu____13322 =
                           FStar_Syntax_Print.args_to_string args in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____13319 uu____13320 uu____13321 uu____13322);
                    (let uu____13323 = FStar_Syntax_Syntax.new_bv_set () in
                     let uu____13326 = FStar_Syntax_Syntax.new_bv_set () in
                     aux [] uu____13323 [] uu____13326 [] all_formals res_t
                       args))) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13360 = lhs in
          match uu____13360 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13370 ->
                    let uu____13371 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13371 rhs in
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
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
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
                             (FStar_String.concat "\n\t>") in
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
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13518
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___107_13576 =
          match uu___107_13576 with
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
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
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
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
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
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
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
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
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
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____15008 ->
                             let uu____15015 =
                               let uu____15020 =
                                 let uu____15021 =
                                   FStar_Syntax_Print.uvar_to_string uv in
                                 let uu____15022 =
                                   FStar_Syntax_Print.term_to_string k1 in
                                 let uu____15023 =
                                   FStar_Syntax_Print.term_to_string k_uv in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____15021 uu____15022 uu____15023 in
                               (FStar_Errors.Fatal_IllTyped, uu____15020) in
                             FStar_Errors.raise_error uu____15015
                               t1.FStar_Syntax_Syntax.pos in
                       let uu____15030 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15030
                         (fun uu____15085  ->
                            match uu____15085 with
                            | (xs1,c1) ->
                                let uu____15134 =
                                  let uu____15175 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15175) in
                                FStar_Pervasives_Native.Some uu____15134)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15296 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15312 = project orig env wl1 i st in
                     match uu____15312 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15326) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15341 = imitate orig env wl1 st in
                  match uu____15341 with
                  | Failed uu____15346 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15377 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15377 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15400 = forced_lhs_pattern in
                    (match uu____15400 with
                     | (lhs_t,uu____15402,uu____15403,uu____15404) ->
                         ((let uu____15406 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel") in
                           if uu____15406
                           then
                             let uu____15407 = lhs1 in
                             match uu____15407 with
                             | (t0,uu____15409,uu____15410,uu____15411) ->
                                 let uu____15412 = forced_lhs_pattern in
                                 (match uu____15412 with
                                  | (t11,uu____15414,uu____15415,uu____15416)
                                      ->
                                      let uu____15417 =
                                        FStar_Syntax_Print.term_to_string t0 in
                                      let uu____15418 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15417 uu____15418)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t in
                           let uu____15426 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars in
                           if uu____15426
                           then
                             ((let uu____15428 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15428
                               then
                                 let uu____15429 =
                                   FStar_Syntax_Print.term_to_string rhs in
                                 let uu____15430 = names_to_string rhs_vars in
                                 let uu____15431 = names_to_string lhs_vars in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15429 uu____15430 uu____15431
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction () in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1 in
                               let uu____15435 =
                                 let uu____15436 =
                                   FStar_TypeChecker_Common.as_tprob orig in
                                 solve_t env uu____15436 wl2 in
                               match uu____15435 with
                               | Failed uu____15437 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15446 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15446
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt)))) in
              let check_head fvs1 t21 =
                let uu____15459 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15459 with
                | (hd1,uu____15475) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15496 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15509 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15510 -> true
                     | uu____15527 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15531 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15531
                         then true
                         else
                           ((let uu____15534 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15534
                             then
                               let uu____15535 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15535
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15555 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15555 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15568 =
                            let uu____15569 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15569 in
                          giveup_or_defer1 orig uu____15568
                        else
                          (let uu____15571 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15571
                           then
                             let uu____15572 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15572
                              then
                                let uu____15573 = subterms args_lhs in
                                imitate' orig env wl1 uu____15573
                              else
                                ((let uu____15578 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15578
                                  then
                                    let uu____15579 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15580 = names_to_string fvs1 in
                                    let uu____15581 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15579 uu____15580 uu____15581
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
                               (let uu____15585 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15585
                                then
                                  ((let uu____15587 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15587
                                    then
                                      let uu____15588 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15589 = names_to_string fvs1 in
                                      let uu____15590 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15588 uu____15589 uu____15590
                                    else ());
                                   (let uu____15592 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15592))
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
                     (let uu____15603 =
                        let uu____15604 = FStar_Syntax_Free.names t1 in
                        check_head uu____15604 t2 in
                      if uu____15603
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15615 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15615
                          then
                            let uu____15616 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15617 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15616 uu____15617
                          else ());
                         (let uu____15625 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15625))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15702 uu____15703 r =
               match (uu____15702, uu____15703) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15901 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15901
                   then
                     let uu____15902 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15902
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15926 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15926
                       then
                         let uu____15927 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15928 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15929 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15930 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15931 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15927 uu____15928 uu____15929 uu____15930
                           uu____15931
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15991 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15991 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16005 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____16005 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16059 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16059 in
                                  let uu____16062 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16062 k3)
                           else
                             (let uu____16066 =
                                let uu____16067 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16068 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16069 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16067 uu____16068 uu____16069 in
                              failwith uu____16066) in
                       let uu____16070 =
                         let uu____16077 =
                           let uu____16090 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16090 in
                         match uu____16077 with
                         | (bs,k1') ->
                             let uu____16115 =
                               let uu____16128 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16128 in
                             (match uu____16115 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16156 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____16156 in
                                  let uu____16165 =
                                    let uu____16170 =
                                      let uu____16171 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16171.FStar_Syntax_Syntax.n in
                                    let uu____16174 =
                                      let uu____16175 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16175.FStar_Syntax_Syntax.n in
                                    (uu____16170, uu____16174) in
                                  (match uu____16165 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16184,uu____16185) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16188,FStar_Syntax_Syntax.Tm_type
                                      uu____16189) -> (k2'_ys, [sub_prob])
                                   | uu____16192 ->
                                       let uu____16197 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16197 with
                                        | (t,uu____16209) ->
                                            let uu____16210 = new_uvar r zs t in
                                            (match uu____16210 with
                                             | (k_zs,uu____16222) ->
                                                 let kprob =
                                                   let uu____16224 =
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
                                                          _0_64) uu____16224 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16070 with
                       | (k_u',sub_probs) ->
                           let uu____16241 =
                             let uu____16252 =
                               let uu____16253 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16253 in
                             let uu____16262 =
                               let uu____16265 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16265 in
                             let uu____16268 =
                               let uu____16271 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16271 in
                             (uu____16252, uu____16262, uu____16268) in
                           (match uu____16241 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16290 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16290 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16309 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16309
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16313 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16313 with
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
             let solve_one_pat uu____16366 uu____16367 =
               match (uu____16366, uu____16367) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16485 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16485
                     then
                       let uu____16486 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16487 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16486 uu____16487
                     else ());
                    (let uu____16489 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16489
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16508  ->
                              fun uu____16509  ->
                                match (uu____16508, uu____16509) with
                                | ((a,uu____16527),(t21,uu____16529)) ->
                                    let uu____16538 =
                                      let uu____16543 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16543
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16538
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16549 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16549 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16564 = occurs_check env wl (u1, k1) t21 in
                        match uu____16564 with
                        | (occurs_ok,uu____16572) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16580 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16580
                            then
                              let sol =
                                let uu____16582 =
                                  let uu____16591 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16591) in
                                TERM uu____16582 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16598 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16598
                               then
                                 let uu____16599 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16599 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16623,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16649 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16649
                                       then
                                         let uu____16650 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16650
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16657 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16659 = lhs in
             match uu____16659 with
             | (t1,u1,k1,args1) ->
                 let uu____16664 = rhs in
                 (match uu____16664 with
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
                       | uu____16704 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16714 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16714 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16732) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16739 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16739
                                    then
                                      let uu____16740 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16740
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16747 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16749 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16749
        then
          let uu____16750 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16750
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16754 = FStar_Util.physical_equality t1 t2 in
           if uu____16754
           then
             let uu____16755 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16755
           else
             ((let uu____16758 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16758
               then
                 let uu____16759 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16759
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16762,uu____16763) ->
                   let uu____16790 =
                     let uu___144_16791 = problem in
                     let uu____16792 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___144_16791.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16792;
                       FStar_TypeChecker_Common.relation =
                         (uu___144_16791.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___144_16791.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___144_16791.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___144_16791.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___144_16791.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___144_16791.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___144_16791.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___144_16791.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16790 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16793,uu____16794) ->
                   let uu____16801 =
                     let uu___144_16802 = problem in
                     let uu____16803 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___144_16802.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16803;
                       FStar_TypeChecker_Common.relation =
                         (uu___144_16802.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___144_16802.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___144_16802.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___144_16802.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___144_16802.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___144_16802.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___144_16802.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___144_16802.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16801 wl
               | (uu____16804,FStar_Syntax_Syntax.Tm_ascribed uu____16805) ->
                   let uu____16832 =
                     let uu___145_16833 = problem in
                     let uu____16834 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16833.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___145_16833.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16833.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16834;
                       FStar_TypeChecker_Common.element =
                         (uu___145_16833.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16833.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16833.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16833.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16833.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16833.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16832 wl
               | (uu____16835,FStar_Syntax_Syntax.Tm_meta uu____16836) ->
                   let uu____16843 =
                     let uu___145_16844 = problem in
                     let uu____16845 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16844.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___145_16844.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16844.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16845;
                       FStar_TypeChecker_Common.element =
                         (uu___145_16844.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16844.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16844.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16844.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16844.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16844.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16843 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16846,uu____16847) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16848,FStar_Syntax_Syntax.Tm_bvar uu____16849) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___108_16904 =
                     match uu___108_16904 with
                     | [] -> c
                     | bs ->
                         let uu____16926 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16926 in
                   let uu____16935 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16935 with
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
                                   let uu____17077 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17077
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17079 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____17079))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___109_17155 =
                     match uu___109_17155 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17189 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17189 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17325 =
                                   let uu____17330 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17331 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17330
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17331 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____17325))
               | (FStar_Syntax_Syntax.Tm_abs uu____17336,uu____17337) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17362 -> true
                     | uu____17379 -> false in
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
                       (let uu____17426 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___146_17434 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___146_17434.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___146_17434.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___146_17434.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___146_17434.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___146_17434.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___146_17434.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___146_17434.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___146_17434.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___146_17434.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___146_17434.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___146_17434.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___146_17434.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___146_17434.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___146_17434.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___146_17434.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___146_17434.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___146_17434.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___146_17434.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___146_17434.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___146_17434.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___146_17434.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___146_17434.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___146_17434.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___146_17434.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___146_17434.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___146_17434.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___146_17434.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___146_17434.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___146_17434.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___146_17434.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___146_17434.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17426 with
                        | (uu____17437,ty,uu____17439) ->
                            let uu____17440 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17440) in
                   let uu____17441 =
                     let uu____17458 = maybe_eta t1 in
                     let uu____17465 = maybe_eta t2 in
                     (uu____17458, uu____17465) in
                   (match uu____17441 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___147_17507 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___147_17507.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___147_17507.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___147_17507.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___147_17507.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___147_17507.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___147_17507.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___147_17507.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___147_17507.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17530 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17530
                        then
                          let uu____17531 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17531 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17546 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17546.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17546.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17546.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17546.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17546.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17546.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17546.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17546.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17570 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17570
                        then
                          let uu____17571 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17571 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17586 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17586.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17586.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17586.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17586.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17586.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17586.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17586.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17586.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17590 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17607,FStar_Syntax_Syntax.Tm_abs uu____17608) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17633 -> true
                     | uu____17650 -> false in
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
                       (let uu____17697 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___146_17705 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___146_17705.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___146_17705.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___146_17705.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___146_17705.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___146_17705.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___146_17705.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___146_17705.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___146_17705.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___146_17705.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___146_17705.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___146_17705.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___146_17705.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___146_17705.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___146_17705.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___146_17705.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___146_17705.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___146_17705.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___146_17705.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___146_17705.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___146_17705.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___146_17705.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___146_17705.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___146_17705.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___146_17705.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___146_17705.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___146_17705.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___146_17705.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___146_17705.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___146_17705.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___146_17705.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___146_17705.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17697 with
                        | (uu____17708,ty,uu____17710) ->
                            let uu____17711 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17711) in
                   let uu____17712 =
                     let uu____17729 = maybe_eta t1 in
                     let uu____17736 = maybe_eta t2 in
                     (uu____17729, uu____17736) in
                   (match uu____17712 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___147_17778 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___147_17778.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___147_17778.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___147_17778.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___147_17778.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___147_17778.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___147_17778.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___147_17778.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___147_17778.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17801 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17801
                        then
                          let uu____17802 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17802 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17817 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17817.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17817.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17817.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17817.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17817.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17817.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17817.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17817.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17841 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17841
                        then
                          let uu____17842 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17842 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17857 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17857.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17857.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17857.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17857.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17857.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17857.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17857.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17857.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17861 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____17893 = FStar_Syntax_Free.uvars t1 in
                       FStar_Util.set_is_empty uu____17893) &&
                        (let uu____17905 = FStar_Syntax_Free.uvars t2 in
                         FStar_Util.set_is_empty uu____17905))
                       &&
                       (let uu____17920 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort in
                        match uu____17920 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___110_17930 =
                              match uu___110_17930 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____17931 -> true
                              | uu____17932 -> false in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____17933 -> false) in
                   let uu____17934 = as_refinement should_delta env wl t1 in
                   (match uu____17934 with
                    | (x11,phi1) ->
                        let uu____17941 =
                          as_refinement should_delta env wl t2 in
                        (match uu____17941 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____17949 =
                                 mk_problem (p_scope orig) orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17949 in
                             let x12 = FStar_Syntax_Syntax.freshen_bv x11 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x12)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi22 =
                               FStar_Syntax_Subst.subst subst1 phi21 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x12 in
                             let mk_imp1 imp phi12 phi23 =
                               let uu____17987 = imp phi12 phi23 in
                               FStar_All.pipe_right uu____17987
                                 (guard_on_element wl problem x12) in
                             let fallback uu____17991 =
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
                                       let uu____18019 =
                                         FStar_Syntax_Syntax.mk_binder x12 in
                                       [uu____18019] in
                                     FStar_List.append (p_scope orig)
                                       uu____18012 in
                                   mk_problem uu____18011 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____18006 in
                               let uu____18028 =
                                 solve env1
                                   (let uu___149_18030 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___149_18030.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___149_18030.smt_ok);
                                      tcenv = (uu___149_18030.tcenv)
                                    }) in
                               (match uu____18028 with
                                | Failed uu____18037 -> fallback ()
                                | Success uu____18042 ->
                                    let guard =
                                      let uu____18046 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____18051 =
                                        let uu____18052 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____18052
                                          (guard_on_element wl problem x12) in
                                      FStar_Syntax_Util.mk_conj uu____18046
                                        uu____18051 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___150_18061 = wl1 in
                                      {
                                        attempting =
                                          (uu___150_18061.attempting);
                                        wl_deferred =
                                          (uu___150_18061.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___150_18061.defer_ok);
                                        smt_ok = (uu___150_18061.smt_ok);
                                        tcenv = (uu___150_18061.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18063,FStar_Syntax_Syntax.Tm_uvar uu____18064) ->
                   let uu____18097 = destruct_flex_t t1 in
                   let uu____18098 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18097 uu____18098
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18099;
                     FStar_Syntax_Syntax.pos = uu____18100;
                     FStar_Syntax_Syntax.vars = uu____18101;_},uu____18102),FStar_Syntax_Syntax.Tm_uvar
                  uu____18103) ->
                   let uu____18156 = destruct_flex_t t1 in
                   let uu____18157 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18156 uu____18157
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18158,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18159;
                     FStar_Syntax_Syntax.pos = uu____18160;
                     FStar_Syntax_Syntax.vars = uu____18161;_},uu____18162))
                   ->
                   let uu____18215 = destruct_flex_t t1 in
                   let uu____18216 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18215 uu____18216
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18217;
                     FStar_Syntax_Syntax.pos = uu____18218;
                     FStar_Syntax_Syntax.vars = uu____18219;_},uu____18220),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18221;
                     FStar_Syntax_Syntax.pos = uu____18222;
                     FStar_Syntax_Syntax.vars = uu____18223;_},uu____18224))
                   ->
                   let uu____18297 = destruct_flex_t t1 in
                   let uu____18298 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18297 uu____18298
               | (FStar_Syntax_Syntax.Tm_uvar uu____18299,uu____18300) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18317 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18317 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18324;
                     FStar_Syntax_Syntax.pos = uu____18325;
                     FStar_Syntax_Syntax.vars = uu____18326;_},uu____18327),uu____18328)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18365 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18365 t2 wl
               | (uu____18372,FStar_Syntax_Syntax.Tm_uvar uu____18373) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18390,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18391;
                     FStar_Syntax_Syntax.pos = uu____18392;
                     FStar_Syntax_Syntax.vars = uu____18393;_},uu____18394))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18431,FStar_Syntax_Syntax.Tm_type uu____18432) ->
                   solve_t' env
                     (let uu___151_18450 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18450.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18450.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18450.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18450.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18450.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18450.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18450.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18450.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18450.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18451;
                     FStar_Syntax_Syntax.pos = uu____18452;
                     FStar_Syntax_Syntax.vars = uu____18453;_},uu____18454),FStar_Syntax_Syntax.Tm_type
                  uu____18455) ->
                   solve_t' env
                     (let uu___151_18493 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18493.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18493.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18493.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18493.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18493.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18493.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18493.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18493.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18493.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18494,FStar_Syntax_Syntax.Tm_arrow uu____18495) ->
                   solve_t' env
                     (let uu___151_18525 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18525.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18525.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18525.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18525.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18525.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18525.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18525.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18525.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18525.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18526;
                     FStar_Syntax_Syntax.pos = uu____18527;
                     FStar_Syntax_Syntax.vars = uu____18528;_},uu____18529),FStar_Syntax_Syntax.Tm_arrow
                  uu____18530) ->
                   solve_t' env
                     (let uu___151_18580 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18580.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18580.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18580.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18580.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18580.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18580.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18580.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18580.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18580.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18581,uu____18582) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18601 =
                        let uu____18602 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18602 in
                      if uu____18601
                      then
                        let uu____18603 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___152_18609 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___152_18609.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___152_18609.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___152_18609.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___152_18609.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___152_18609.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___152_18609.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___152_18609.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___152_18609.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___152_18609.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18610 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18603 uu____18610 t2
                          wl
                      else
                        (let uu____18618 = base_and_refinement env t2 in
                         match uu____18618 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18647 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___153_18653 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___153_18653.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___153_18653.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___153_18653.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___153_18653.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___153_18653.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___153_18653.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___153_18653.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___153_18653.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___153_18653.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18654 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18647
                                    uu____18654 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___154_18668 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___154_18668.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___154_18668.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18671 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18671 in
                                  let guard =
                                    let uu____18683 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18683
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18691;
                     FStar_Syntax_Syntax.pos = uu____18692;
                     FStar_Syntax_Syntax.vars = uu____18693;_},uu____18694),uu____18695)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18734 =
                        let uu____18735 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18735 in
                      if uu____18734
                      then
                        let uu____18736 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___152_18742 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___152_18742.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___152_18742.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___152_18742.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___152_18742.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___152_18742.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___152_18742.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___152_18742.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___152_18742.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___152_18742.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18743 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18736 uu____18743 t2
                          wl
                      else
                        (let uu____18751 = base_and_refinement env t2 in
                         match uu____18751 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18780 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___153_18786 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___153_18786.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___153_18786.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___153_18786.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___153_18786.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___153_18786.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___153_18786.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___153_18786.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___153_18786.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___153_18786.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18787 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18780
                                    uu____18787 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___154_18801 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___154_18801.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___154_18801.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18804 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18804 in
                                  let guard =
                                    let uu____18816 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18816
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18824,FStar_Syntax_Syntax.Tm_uvar uu____18825) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18843 = base_and_refinement env t1 in
                      match uu____18843 with
                      | (t_base,uu____18855) ->
                          solve_t env
                            (let uu___155_18869 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18869.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___155_18869.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18869.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18869.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18869.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18869.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18869.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18869.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18870,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18871;
                     FStar_Syntax_Syntax.pos = uu____18872;
                     FStar_Syntax_Syntax.vars = uu____18873;_},uu____18874))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18912 = base_and_refinement env t1 in
                      match uu____18912 with
                      | (t_base,uu____18924) ->
                          solve_t env
                            (let uu___155_18938 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18938.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___155_18938.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18938.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18938.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18938.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18938.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18938.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18938.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18939,uu____18940) ->
                   let t21 =
                     let uu____18950 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18950 in
                   solve_t env
                     (let uu___156_18974 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___156_18974.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___156_18974.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___156_18974.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___156_18974.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___156_18974.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___156_18974.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___156_18974.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___156_18974.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___156_18974.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18975,FStar_Syntax_Syntax.Tm_refine uu____18976) ->
                   let t11 =
                     let uu____18986 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18986 in
                   solve_t env
                     (let uu___157_19010 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_19010.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___157_19010.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___157_19010.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___157_19010.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_19010.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_19010.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_19010.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_19010.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_19010.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____19013,uu____19014) ->
                   let head1 =
                     let uu____19040 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19040
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19084 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19084
                       FStar_Pervasives_Native.fst in
                   let uu____19125 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19125
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19140 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19140
                      then
                        let guard =
                          let uu____19152 =
                            let uu____19153 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19153 = FStar_Syntax_Util.Equal in
                          if uu____19152
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19157 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____19157) in
                        let uu____19160 = solve_prob orig guard [] wl in
                        solve env uu____19160
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19163,uu____19164) ->
                   let head1 =
                     let uu____19174 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19174
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19218 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19218
                       FStar_Pervasives_Native.fst in
                   let uu____19259 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19259
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19274 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19274
                      then
                        let guard =
                          let uu____19286 =
                            let uu____19287 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19287 = FStar_Syntax_Util.Equal in
                          if uu____19286
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19291 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____19291) in
                        let uu____19294 = solve_prob orig guard [] wl in
                        solve env uu____19294
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19297,uu____19298) ->
                   let head1 =
                     let uu____19302 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19302
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19346 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19346
                       FStar_Pervasives_Native.fst in
                   let uu____19387 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19387
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19402 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19402
                      then
                        let guard =
                          let uu____19414 =
                            let uu____19415 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19415 = FStar_Syntax_Util.Equal in
                          if uu____19414
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19419 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19419) in
                        let uu____19422 = solve_prob orig guard [] wl in
                        solve env uu____19422
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19425,uu____19426) ->
                   let head1 =
                     let uu____19430 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19430
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19474 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19474
                       FStar_Pervasives_Native.fst in
                   let uu____19515 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19515
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19530 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19530
                      then
                        let guard =
                          let uu____19542 =
                            let uu____19543 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19543 = FStar_Syntax_Util.Equal in
                          if uu____19542
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19547 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19547) in
                        let uu____19550 = solve_prob orig guard [] wl in
                        solve env uu____19550
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19553,uu____19554) ->
                   let head1 =
                     let uu____19558 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19558
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19602 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19602
                       FStar_Pervasives_Native.fst in
                   let uu____19643 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19643
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19658 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19658
                      then
                        let guard =
                          let uu____19670 =
                            let uu____19671 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19671 = FStar_Syntax_Util.Equal in
                          if uu____19670
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19675 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19675) in
                        let uu____19678 = solve_prob orig guard [] wl in
                        solve env uu____19678
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19681,uu____19682) ->
                   let head1 =
                     let uu____19700 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19700
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19744 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19744
                       FStar_Pervasives_Native.fst in
                   let uu____19785 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19785
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19800 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19800
                      then
                        let guard =
                          let uu____19812 =
                            let uu____19813 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19813 = FStar_Syntax_Util.Equal in
                          if uu____19812
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19817 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19817) in
                        let uu____19820 = solve_prob orig guard [] wl in
                        solve env uu____19820
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19823,FStar_Syntax_Syntax.Tm_match uu____19824) ->
                   let head1 =
                     let uu____19850 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19850
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19894 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19894
                       FStar_Pervasives_Native.fst in
                   let uu____19935 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19935
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19950 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19950
                      then
                        let guard =
                          let uu____19962 =
                            let uu____19963 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19963 = FStar_Syntax_Util.Equal in
                          if uu____19962
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19967 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19967) in
                        let uu____19970 = solve_prob orig guard [] wl in
                        solve env uu____19970
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19973,FStar_Syntax_Syntax.Tm_uinst uu____19974) ->
                   let head1 =
                     let uu____19984 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19984
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20028 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20028
                       FStar_Pervasives_Native.fst in
                   let uu____20069 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20069
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20084 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20084
                      then
                        let guard =
                          let uu____20096 =
                            let uu____20097 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20097 = FStar_Syntax_Util.Equal in
                          if uu____20096
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20101 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____20101) in
                        let uu____20104 = solve_prob orig guard [] wl in
                        solve env uu____20104
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20107,FStar_Syntax_Syntax.Tm_name uu____20108) ->
                   let head1 =
                     let uu____20112 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20112
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20156 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20156
                       FStar_Pervasives_Native.fst in
                   let uu____20197 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20197
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20212 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20212
                      then
                        let guard =
                          let uu____20224 =
                            let uu____20225 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20225 = FStar_Syntax_Util.Equal in
                          if uu____20224
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20229 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20229) in
                        let uu____20232 = solve_prob orig guard [] wl in
                        solve env uu____20232
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20235,FStar_Syntax_Syntax.Tm_constant uu____20236) ->
                   let head1 =
                     let uu____20240 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20240
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20284 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20284
                       FStar_Pervasives_Native.fst in
                   let uu____20325 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20325
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20340 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20340
                      then
                        let guard =
                          let uu____20352 =
                            let uu____20353 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20353 = FStar_Syntax_Util.Equal in
                          if uu____20352
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20357 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20357) in
                        let uu____20360 = solve_prob orig guard [] wl in
                        solve env uu____20360
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20363,FStar_Syntax_Syntax.Tm_fvar uu____20364) ->
                   let head1 =
                     let uu____20368 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20368
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20412 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20412
                       FStar_Pervasives_Native.fst in
                   let uu____20453 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20453
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20468 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20468
                      then
                        let guard =
                          let uu____20480 =
                            let uu____20481 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20481 = FStar_Syntax_Util.Equal in
                          if uu____20480
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20485 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20485) in
                        let uu____20488 = solve_prob orig guard [] wl in
                        solve env uu____20488
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20491,FStar_Syntax_Syntax.Tm_app uu____20492) ->
                   let head1 =
                     let uu____20510 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20510
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20554 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20554
                       FStar_Pervasives_Native.fst in
                   let uu____20595 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20595
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20610 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20610
                      then
                        let guard =
                          let uu____20622 =
                            let uu____20623 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20623 = FStar_Syntax_Util.Equal in
                          if uu____20622
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20627 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20627) in
                        let uu____20630 = solve_prob orig guard [] wl in
                        solve env uu____20630
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20633,uu____20634) ->
                   let uu____20647 =
                     let uu____20648 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20649 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20648
                       uu____20649 in
                   failwith uu____20647
               | (FStar_Syntax_Syntax.Tm_delayed uu____20650,uu____20651) ->
                   let uu____20676 =
                     let uu____20677 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20678 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20677
                       uu____20678 in
                   failwith uu____20676
               | (uu____20679,FStar_Syntax_Syntax.Tm_delayed uu____20680) ->
                   let uu____20705 =
                     let uu____20706 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20707 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20706
                       uu____20707 in
                   failwith uu____20705
               | (uu____20708,FStar_Syntax_Syntax.Tm_let uu____20709) ->
                   let uu____20722 =
                     let uu____20723 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20724 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20723
                       uu____20724 in
                   failwith uu____20722
               | uu____20725 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20761 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20761
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20763 =
               let uu____20764 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20765 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20764 uu____20765 in
             giveup env uu____20763 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20785  ->
                    fun uu____20786  ->
                      match (uu____20785, uu____20786) with
                      | ((a1,uu____20804),(a2,uu____20806)) ->
                          let uu____20815 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20815)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20825 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20825 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20849 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20856)::[] -> wp1
              | uu____20873 ->
                  let uu____20882 =
                    let uu____20883 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20883 in
                  failwith uu____20882 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20891 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____20891]
              | x -> x in
            let uu____20893 =
              let uu____20902 =
                let uu____20903 =
                  let uu____20904 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20904 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20903 in
              [uu____20902] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20893;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20905 = lift_c1 () in solve_eq uu____20905 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___111_20911  ->
                       match uu___111_20911 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20912 -> false)) in
             let uu____20913 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20947)::uu____20948,(wp2,uu____20950)::uu____20951)
                   -> (wp1, wp2)
               | uu____21008 ->
                   let uu____21029 =
                     let uu____21034 =
                       let uu____21035 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name in
                       let uu____21036 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21035 uu____21036 in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21034) in
                   FStar_Errors.raise_error uu____21029
                     env.FStar_TypeChecker_Env.range in
             match uu____20913 with
             | (wpc1,wpc2) ->
                 let uu____21055 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____21055
                 then
                   let uu____21058 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____21058 wl
                 else
                   (let uu____21062 =
                      let uu____21069 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____21069 in
                    match uu____21062 with
                    | (c2_decl,qualifiers) ->
                        let uu____21090 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21090
                        then
                          let c1_repr =
                            let uu____21094 =
                              let uu____21095 =
                                let uu____21096 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21096 in
                              let uu____21097 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21095 uu____21097 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21094 in
                          let c2_repr =
                            let uu____21099 =
                              let uu____21100 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21101 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21100 uu____21101 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21099 in
                          let prob =
                            let uu____21103 =
                              let uu____21108 =
                                let uu____21109 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21110 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21109
                                  uu____21110 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21108 in
                            FStar_TypeChecker_Common.TProb uu____21103 in
                          let wl1 =
                            let uu____21112 =
                              let uu____21115 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21115 in
                            solve_prob orig uu____21112 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21124 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21124
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____21127 =
                                     let uu____21130 =
                                       let uu____21131 =
                                         let uu____21146 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21147 =
                                           let uu____21150 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21151 =
                                             let uu____21154 =
                                               let uu____21155 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21155 in
                                             [uu____21154] in
                                           uu____21150 :: uu____21151 in
                                         (uu____21146, uu____21147) in
                                       FStar_Syntax_Syntax.Tm_app uu____21131 in
                                     FStar_Syntax_Syntax.mk uu____21130 in
                                   uu____21127 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____21164 =
                                    let uu____21167 =
                                      let uu____21168 =
                                        let uu____21183 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21184 =
                                          let uu____21187 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21188 =
                                            let uu____21191 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21192 =
                                              let uu____21195 =
                                                let uu____21196 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21196 in
                                              [uu____21195] in
                                            uu____21191 :: uu____21192 in
                                          uu____21187 :: uu____21188 in
                                        (uu____21183, uu____21184) in
                                      FStar_Syntax_Syntax.Tm_app uu____21168 in
                                    FStar_Syntax_Syntax.mk uu____21167 in
                                  uu____21164 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21203 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21203 in
                           let wl1 =
                             let uu____21213 =
                               let uu____21216 =
                                 let uu____21219 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21219 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21216 in
                             solve_prob orig uu____21213 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21232 = FStar_Util.physical_equality c1 c2 in
        if uu____21232
        then
          let uu____21233 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21233
        else
          ((let uu____21236 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21236
            then
              let uu____21237 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21238 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21237
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21238
            else ());
           (let uu____21240 =
              let uu____21245 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21246 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21245, uu____21246) in
            match uu____21240 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21250),FStar_Syntax_Syntax.Total
                    (t2,uu____21252)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21269 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21269 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21272,FStar_Syntax_Syntax.Total uu____21273) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21291),FStar_Syntax_Syntax.Total
                    (t2,uu____21293)) ->
                     let uu____21310 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21310 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21314),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21316)) ->
                     let uu____21333 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21333 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21337),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21339)) ->
                     let uu____21356 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21356 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21359,FStar_Syntax_Syntax.Comp uu____21360) ->
                     let uu____21369 =
                       let uu___158_21374 = problem in
                       let uu____21379 =
                         let uu____21380 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21380 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___158_21374.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21379;
                         FStar_TypeChecker_Common.relation =
                           (uu___158_21374.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___158_21374.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___158_21374.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___158_21374.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___158_21374.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___158_21374.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___158_21374.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___158_21374.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21369 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21381,FStar_Syntax_Syntax.Comp uu____21382) ->
                     let uu____21391 =
                       let uu___158_21396 = problem in
                       let uu____21401 =
                         let uu____21402 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21402 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___158_21396.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21401;
                         FStar_TypeChecker_Common.relation =
                           (uu___158_21396.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___158_21396.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___158_21396.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___158_21396.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___158_21396.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___158_21396.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___158_21396.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___158_21396.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21391 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21403,FStar_Syntax_Syntax.GTotal uu____21404) ->
                     let uu____21413 =
                       let uu___159_21418 = problem in
                       let uu____21423 =
                         let uu____21424 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21424 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_21418.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___159_21418.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___159_21418.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21423;
                         FStar_TypeChecker_Common.element =
                           (uu___159_21418.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_21418.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_21418.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_21418.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_21418.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_21418.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21413 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21425,FStar_Syntax_Syntax.Total uu____21426) ->
                     let uu____21435 =
                       let uu___159_21440 = problem in
                       let uu____21445 =
                         let uu____21446 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21446 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_21440.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___159_21440.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___159_21440.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21445;
                         FStar_TypeChecker_Common.element =
                           (uu___159_21440.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_21440.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_21440.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_21440.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_21440.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_21440.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21435 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21447,FStar_Syntax_Syntax.Comp uu____21448) ->
                     let uu____21449 =
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
                     if uu____21449
                     then
                       let uu____21450 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21450 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21456 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21466 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21467 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21466, uu____21467)) in
                          match uu____21456 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21474 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21474
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21476 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21476 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21479 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21481 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21481) in
                                if uu____21479
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
                                  (let uu____21484 =
                                     let uu____21485 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21486 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21485 uu____21486 in
                                   giveup env uu____21484 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21491 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21529  ->
              match uu____21529 with
              | (uu____21542,uu____21543,u,uu____21545,uu____21546,uu____21547)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21491 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21578 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21578 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21596 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21624  ->
                match uu____21624 with
                | (u1,u2) ->
                    let uu____21631 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21632 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21631 uu____21632)) in
      FStar_All.pipe_right uu____21596 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21649,[])) -> "{}"
      | uu____21674 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21691 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21691
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21694 =
              FStar_List.map
                (fun uu____21704  ->
                   match uu____21704 with
                   | (uu____21709,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21694 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21714 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21714 imps
let new_t_problem:
  'Auu____21722 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21722 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21722)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21756 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21756
                then
                  let uu____21757 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21758 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21757
                    (rel_to_string rel) uu____21758
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
            let uu____21782 =
              let uu____21785 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21785 in
            FStar_Syntax_Syntax.new_bv uu____21782 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21794 =
              let uu____21797 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21797 in
            let uu____21800 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21794 uu____21800 in
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
      fun err  ->
        let probs1 =
          let uu____21830 = FStar_Options.eager_inference () in
          if uu____21830
          then
            let uu___160_21831 = probs in
            {
              attempting = (uu___160_21831.attempting);
              wl_deferred = (uu___160_21831.wl_deferred);
              ctr = (uu___160_21831.ctr);
              defer_ok = false;
              smt_ok = (uu___160_21831.smt_ok);
              tcenv = (uu___160_21831.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21842 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21842
              then
                let uu____21843 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21843
              else ());
             (let result = err (d, s) in
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
          ((let uu____21857 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21857
            then
              let uu____21858 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21858
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____21862 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21862
             then
               let uu____21863 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21863
             else ());
            (let f2 =
               let uu____21866 =
                 let uu____21867 = FStar_Syntax_Util.unmeta f1 in
                 uu____21867.FStar_Syntax_Syntax.n in
               match uu____21866 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21871 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___161_21872 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___161_21872.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___161_21872.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___161_21872.FStar_TypeChecker_Env.implicits)
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
            let uu____21891 =
              let uu____21892 =
                let uu____21893 =
                  let uu____21894 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21894
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21893;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21892 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21891
let with_guard_no_simp:
  'Auu____21921 .
    'Auu____21921 ->
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
            let uu____21941 =
              let uu____21942 =
                let uu____21943 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21943
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21942;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21941
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
          (let uu____21981 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21981
           then
             let uu____21982 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21983 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21982
               uu____21983
           else ());
          (let prob =
             let uu____21986 =
               let uu____21991 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21991 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21986 in
           let g =
             let uu____21999 =
               let uu____22002 = singleton' env prob smt_ok in
               solve_and_commit env uu____22002
                 (fun uu____22004  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21999 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22022 = try_teq true env t1 t2 in
        match uu____22022 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22026 = FStar_TypeChecker_Env.get_range env in
              let uu____22027 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____22026 uu____22027);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22034 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____22034
              then
                let uu____22035 = FStar_Syntax_Print.term_to_string t1 in
                let uu____22036 = FStar_Syntax_Print.term_to_string t2 in
                let uu____22037 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22035
                  uu____22036 uu____22037
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
          let uu____22051 = FStar_TypeChecker_Env.get_range env in
          let uu____22052 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____22051 uu____22052
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22069 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22069
         then
           let uu____22070 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22071 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22070
             uu____22071
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22076 =
             let uu____22081 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22081 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22076 in
         let uu____22086 =
           let uu____22089 = singleton env prob in
           solve_and_commit env uu____22089
             (fun uu____22091  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22086)
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
      fun uu____22120  ->
        match uu____22120 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22159 =
                 let uu____22164 =
                   let uu____22165 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____22166 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22165 uu____22166 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22164) in
               let uu____22167 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____22159 uu____22167) in
            let equiv1 v1 v' =
              let uu____22175 =
                let uu____22180 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22181 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22180, uu____22181) in
              match uu____22175 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22200 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22230 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22230 with
                      | FStar_Syntax_Syntax.U_unif uu____22237 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22266  ->
                                    match uu____22266 with
                                    | (u,v') ->
                                        let uu____22275 = equiv1 v1 v' in
                                        if uu____22275
                                        then
                                          let uu____22278 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22278 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22294 -> [])) in
            let uu____22299 =
              let wl =
                let uu___162_22303 = empty_worklist env in
                {
                  attempting = (uu___162_22303.attempting);
                  wl_deferred = (uu___162_22303.wl_deferred);
                  ctr = (uu___162_22303.ctr);
                  defer_ok = false;
                  smt_ok = (uu___162_22303.smt_ok);
                  tcenv = (uu___162_22303.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22321  ->
                      match uu____22321 with
                      | (lb,v1) ->
                          let uu____22328 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22328 with
                           | USolved wl1 -> ()
                           | uu____22330 -> fail lb v1))) in
            let rec check_ineq uu____22338 =
              match uu____22338 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22347) -> true
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
                      uu____22370,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22372,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22383) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22390,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22398 -> false) in
            let uu____22403 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22418  ->
                      match uu____22418 with
                      | (u,v1) ->
                          let uu____22425 = check_ineq (u, v1) in
                          if uu____22425
                          then true
                          else
                            ((let uu____22428 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22428
                              then
                                let uu____22429 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22430 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22429
                                  uu____22430
                              else ());
                             false))) in
            if uu____22403
            then ()
            else
              ((let uu____22434 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22434
                then
                  ((let uu____22436 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22436);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22446 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22446))
                else ());
               (let uu____22456 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22456))
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
      let fail uu____22504 =
        match uu____22504 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22518 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22518
       then
         let uu____22519 = wl_to_string wl in
         let uu____22520 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22519 uu____22520
       else ());
      (let g1 =
         let uu____22535 = solve_and_commit env wl fail in
         match uu____22535 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___163_22548 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___163_22548.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___163_22548.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___163_22548.FStar_TypeChecker_Env.implicits)
             }
         | uu____22553 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___164_22557 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___164_22557.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___164_22557.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___164_22557.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22583 = FStar_ST.op_Bang last_proof_ns in
    match uu____22583 with
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
            let uu___165_22773 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___165_22773.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___165_22773.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___165_22773.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22774 =
            let uu____22775 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22775 in
          if uu____22774
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22783 = FStar_TypeChecker_Env.get_range env in
                     let uu____22784 =
                       let uu____22785 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22785 in
                     FStar_Errors.diag uu____22783 uu____22784)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22789 = FStar_TypeChecker_Env.get_range env in
                      let uu____22790 =
                        let uu____22791 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22791 in
                      FStar_Errors.diag uu____22789 uu____22790)
                   else ();
                   (let uu____22793 = check_trivial vc1 in
                    match uu____22793 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22800 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22801 =
                                let uu____22802 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22802 in
                              FStar_Errors.diag uu____22800 uu____22801)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22807 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22808 =
                                let uu____22809 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22809 in
                              FStar_Errors.diag uu____22807 uu____22808)
                           else ();
                           (let vcs =
                              let uu____22820 = FStar_Options.use_tactics () in
                              if uu____22820
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22839  ->
                                     (let uu____22841 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22841);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22843 =
                                   let uu____22850 = FStar_Options.peek () in
                                   (env, vc2, uu____22850) in
                                 [uu____22843]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22884  ->
                                    match uu____22884 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22895 = check_trivial goal1 in
                                        (match uu____22895 with
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
                                                (let uu____22903 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22904 =
                                                   let uu____22905 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22906 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22905 uu____22906 in
                                                 FStar_Errors.diag
                                                   uu____22903 uu____22904)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22909 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22910 =
                                                   let uu____22911 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22911 in
                                                 FStar_Errors.diag
                                                   uu____22909 uu____22910)
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
      let uu____22921 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22921 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22927 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22927
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22934 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22934 with
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
          let uu____22953 = FStar_Syntax_Unionfind.find u in
          match uu____22953 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22956 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22974 = acc in
          match uu____22974 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23060 = hd1 in
                   (match uu____23060 with
                    | (uu____23073,env,u,tm,k,r) ->
                        let uu____23079 = unresolved u in
                        if uu____23079
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____23110 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____23110
                            then
                              let uu____23111 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23112 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23113 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23111 uu____23112 uu____23113
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___166_23116 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___166_23116.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___166_23116.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___166_23116.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___166_23116.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___166_23116.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___166_23116.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___166_23116.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___166_23116.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___166_23116.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___166_23116.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___166_23116.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___166_23116.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___166_23116.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___166_23116.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___166_23116.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___166_23116.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___166_23116.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___166_23116.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___166_23116.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___166_23116.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___166_23116.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___166_23116.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___166_23116.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___166_23116.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___166_23116.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___166_23116.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___166_23116.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___166_23116.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___166_23116.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___166_23116.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___166_23116.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___166_23116.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___166_23116.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              try
                                if must_total
                                then
                                  let uu____23125 =
                                    env2.FStar_TypeChecker_Env.type_of
                                      (let uu___169_23133 = env2 in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___169_23133.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___169_23133.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___169_23133.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___169_23133.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___169_23133.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___169_23133.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___169_23133.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___169_23133.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.is_pattern =
                                           (uu___169_23133.FStar_TypeChecker_Env.is_pattern);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___169_23133.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___169_23133.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___169_23133.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (uu___169_23133.FStar_TypeChecker_Env.letrecs);
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___169_23133.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___169_23133.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___169_23133.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___169_23133.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___169_23133.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___169_23133.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___169_23133.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___169_23133.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___169_23133.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___169_23133.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___169_23133.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___169_23133.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           true;
                                         FStar_TypeChecker_Env.qname_and_index
                                           =
                                           (uu___169_23133.FStar_TypeChecker_Env.qname_and_index);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___169_23133.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth =
                                           (uu___169_23133.FStar_TypeChecker_Env.synth);
                                         FStar_TypeChecker_Env.is_native_tactic
                                           =
                                           (uu___169_23133.FStar_TypeChecker_Env.is_native_tactic);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___169_23133.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___169_23133.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___169_23133.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.dep_graph =
                                           (uu___169_23133.FStar_TypeChecker_Env.dep_graph)
                                       }) tm1 in
                                  match uu____23125 with
                                  | (uu____23134,uu____23135,g1) -> g1
                                else
                                  (let uu____23138 =
                                     env2.FStar_TypeChecker_Env.tc_term
                                       (let uu___170_23146 = env2 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___170_23146.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___170_23146.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___170_23146.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___170_23146.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___170_23146.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___170_23146.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___170_23146.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___170_23146.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.is_pattern =
                                            (uu___170_23146.FStar_TypeChecker_Env.is_pattern);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___170_23146.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___170_23146.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___170_23146.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___170_23146.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___170_23146.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___170_23146.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___170_23146.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___170_23146.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___170_23146.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___170_23146.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___170_23146.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___170_23146.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___170_23146.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___170_23146.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___170_23146.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___170_23146.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            = true;
                                          FStar_TypeChecker_Env.qname_and_index
                                            =
                                            (uu___170_23146.FStar_TypeChecker_Env.qname_and_index);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___170_23146.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth =
                                            (uu___170_23146.FStar_TypeChecker_Env.synth);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___170_23146.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___170_23146.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___170_23146.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___170_23146.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.dep_graph =
                                            (uu___170_23146.FStar_TypeChecker_Env.dep_graph)
                                        }) tm1 in
                                   match uu____23138 with
                                   | (uu____23147,uu____23148,g1) -> g1)
                              with
                              | e ->
                                  ((let uu____23156 =
                                      let uu____23165 =
                                        let uu____23172 =
                                          let uu____23173 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u in
                                          let uu____23174 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env2 tm1 in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23173 uu____23174 in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23172, r) in
                                      [uu____23165] in
                                    FStar_Errors.add_errors uu____23156);
                                   FStar_Exn.raise e) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___171_23188 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___171_23188.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___171_23188.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___171_23188.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23191 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23197  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23191 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___172_23225 = g in
        let uu____23226 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_23225.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_23225.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___172_23225.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23226
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
        let uu____23280 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23280 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23293 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23293
      | (reason,uu____23295,uu____23296,e,t,r)::uu____23300 ->
          let uu____23327 =
            let uu____23332 =
              let uu____23333 = FStar_Syntax_Print.term_to_string t in
              let uu____23334 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23333 uu____23334 in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23332) in
          FStar_Errors.raise_error uu____23327 r
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___173_23341 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___173_23341.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___173_23341.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___173_23341.FStar_TypeChecker_Env.implicits)
      }
let discharge_guard_nosmt:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun env  ->
    fun g  ->
      let uu____23364 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23364 with
      | FStar_Pervasives_Native.Some uu____23369 -> true
      | FStar_Pervasives_Native.None  -> false
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23379 = try_teq false env t1 t2 in
        match uu____23379 with
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
        (let uu____23399 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23399
         then
           let uu____23400 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23401 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23400
             uu____23401
         else ());
        (let uu____23403 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23403 with
         | (prob,x) ->
             let g =
               let uu____23419 =
                 let uu____23422 = singleton' env prob true in
                 solve_and_commit env uu____23422
                   (fun uu____23424  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23419 in
             ((let uu____23434 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____23434
               then
                 let uu____23435 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____23436 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____23437 =
                   let uu____23438 = FStar_Util.must g in
                   guard_to_string env uu____23438 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23435 uu____23436 uu____23437
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
        let uu____23466 = check_subtyping env t1 t2 in
        match uu____23466 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23485 =
              let uu____23486 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____23486 g in
            FStar_Pervasives_Native.Some uu____23485
let get_subtyping_prop:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23498 = check_subtyping env t1 t2 in
        match uu____23498 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23517 =
              let uu____23518 =
                let uu____23519 = FStar_Syntax_Syntax.mk_binder x in
                [uu____23519] in
              close_guard env uu____23518 g in
            FStar_Pervasives_Native.Some uu____23517
let subtype_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23530 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23530
         then
           let uu____23531 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23532 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23531
             uu____23532
         else ());
        (let uu____23534 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23534 with
         | (prob,x) ->
             let g =
               let uu____23544 =
                 let uu____23547 = singleton' env prob false in
                 solve_and_commit env uu____23547
                   (fun uu____23549  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23544 in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23560 =
                      let uu____23561 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____23561] in
                    close_guard env uu____23560 g1 in
                  discharge_guard_nosmt env g2))